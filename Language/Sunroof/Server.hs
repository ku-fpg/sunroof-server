
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeFamilies #-}

-- | The Sunroof server module provides infrastructure to use
--   Sunroof together with kansas-comet.
--
--   It supports setting up a simple server with 'sunroofServer'
--   and provides basic functions for serverside communication
--   with the connected website ('syncJS', 'asyncJS' and 'rsyncJS').
--
--   This module also provides the abstractions for 'Downlink'
--   and 'Uplink'. They represent directed channels for sending data
--   from the server to the website and the other way aroun.
--   The sent data is queued and operations block properly if there
--   is no data available.
module Language.Sunroof.Server
  (
  -- * Basic Comet Server
    syncJS
  , asyncJS
  , rsyncJS
  , SunroofResult(..)
  , SunroofEngine(..)
  , jsonToJS
  , sunroofServer
  , SunroofServerOptions(..)
  , SunroofApp
  , debugSunroofEngine
  -- * Downlink
  , Downlink
  , newDownlink
  , getDownlink
  , putDownlink
  -- * Uplink
  , Uplink
  , newUplink
  , getUplink
  , putUplink
  -- * Timing
  , Timings(..)
  , newTimings
  , resetTimings
  , getTimings
  ) where

import Data.Aeson.Types ( Value(..), Object, Array )
import Data.List ( intercalate )
import Data.Text ( unpack, pack )
import Data.Proxy ( Proxy(..) )
import Data.Default ( Default(..) )
import Data.Semigroup
import Data.Time.Clock
import Data.Scientific ( toRealFloat )
import qualified Data.Vector as V
import qualified Data.HashMap.Strict as M
import System.FilePath((</>))

import Control.Monad.IO.Class ( liftIO )
import Control.Concurrent.STM

import Network.Wai.Handler.Warp ( Port, setPort )
import Network.Wai.Middleware.Static
import qualified Web.Scotty as SC
import Web.Scotty.Comet
  ( send, connect
  , Document, Options
  , kCometPlugin )
import qualified Web.Scotty.Comet as KC

import Language.Sunroof
import Language.Sunroof.JS.Args
import Language.Sunroof.JavaScript
  ( Expr
  , literal, showExpr
  , scopeForEffect )
import Language.Sunroof.Classes ( Uniq )
import Language.Sunroof.Compiler ( compileJS )

-- -------------------------------------------------------------
-- Communication and Compilation
-- -------------------------------------------------------------

-- | The 'SunroofEngine' provides the verbosity level and
--   kansas comet document to the 'SunroofApp'.
data SunroofEngine = SunroofEngine
  { cometDocument :: Document
  -- ^ The document comet uses to manage the connected website.
  , uVar          :: TVar Uniq
  -- ^ Unique number supply for our engine
  , engineVerbose :: Int
  -- ^ @0@ for none, @1@ for initializations,
  --   @2@ for commands done and @3@ for a complete log.
  , compilerOpts  :: CompilerOpts
  -- ^ The options used to setup the compiler.
  , timings       :: Maybe (TVar (Timings NominalDiffTime))
  -- ^ Performance timings of the compiler and communication.
  }

-- | Generate one unique integer from the document.
docUniq :: SunroofEngine -> IO Int
docUniq = docUniqs 1

-- | Generate n unique integers from the document.
docUniqs :: Int -> SunroofEngine -> IO Int
docUniqs n doc = atomically $ do
        u <- readTVar (uVar doc)
        writeTVar (uVar doc) (u + n)
        return u

-- | The number of uniques allocated for the first try of a compilation.
compileUniqAlloc :: Uniq
compileUniqAlloc = 32

-- | Log the given message on the given level
sunroofLog :: SunroofEngine -> Int -> String -> IO ()
sunroofLog engine level msg =
  if (engineVerbose engine >= level)
    then do
      putStr "Sunroof> "
      putStrLn msg
    else return ()

-- | Log the compilation result and return it
compileLog :: SunroofEngine -> String -> IO ()
compileLog engine src = do
  sequence_ $ fmap (sunroofLog engine 3) $
    [ "Compiled:", src]
  return ()

-- | Compile js using unique variables each time.
compileRequestJS :: SunroofEngine -> JS t () -> IO String
compileRequestJS engine jsm = do
  -- Allocate a standard amount of uniq for compilation
  uq <- docUniqs compileUniqAlloc engine
  -- Compile
  (stmts, uq') <- compileJS (compilerOpts engine) uq return jsm
  -- Check if the allocated amount was sufficient
  let txt = showExpr False $ scopeForEffect stmts

  if (uq' < uq + compileUniqAlloc)
    -- It was sufficient we are finished
    then do compileLog engine txt
            return txt
    -- It wasn't sufficient
    else do
      -- Allocate all that are needed
      newUq <- docUniqs (uq' - uq) engine
      -- Compile again
      (stmts', _) <- compileJS (compilerOpts engine) newUq return jsm
      let txt' = showExpr False $ scopeForEffect stmts'
      compileLog engine txt'
      return txt'

-- | Executes the Javascript in the browser without waiting for a result.
asyncJS :: SunroofEngine -> JS t () -> IO ()
asyncJS engine jsm = do
  t0 <- getCurrentTime
  src <- compileRequestJS engine jsm
  addCompileTime engine t0

  t1 <- getCurrentTime
  send (cometDocument engine) (pack src)  -- send it, and forget it
  addSendTime engine t1
  return ()

-- | Executes the Javascript in the browser and waits for the result value.
--   The result value is given the corresponding Haskell type,
--   if possible (see 'SunroofResult').
syncJS :: forall a t . (SunroofResult a) => SunroofEngine -> JS t a -> IO (ResultOf a)
{-
syncJS engine jsm | typesOf (Proxy :: Proxy a) == [Unit] = do
  _ <- syncJS engine (jsm >> return (0 :: JSNumber))
  return $ jsonToValue (Proxy :: Proxy a) Null
-}
syncJS engine jsm = do
  up <- newUplink engine
  t0 <- getCurrentTime
  src <- compileRequestJS engine $ do
          v <- jsm
          up # putUplink v
  addCompileTime engine t0
  t1 <- getCurrentTime
  send (cometDocument engine) (pack src)
  addSendTime engine t1
  t2 <- getCurrentTime
  -- There is *no* race condition in here. If no-one is listening,
  -- then the numbered event gets queued up.
  r <- getUplink up
  addWaitTime engine t2
  return r

-- | Executes the Javascript in the browser and waits for the result.
--   The returned value is just a reference to the computed value.
--   This allows to precompile values like function in the browser.
rsyncJS :: forall a t . (Sunroof a) => SunroofEngine -> JS t a -> IO a
rsyncJS engine jsm = do
  uq <- docUniq engine   -- uniq for the value
  let uq_lab = label ("remote_" <> cast (js uq))
  up :: Uplink JSNumber <- newUplink engine

  t0 <- getCurrentTime
  src <- compileRequestJS engine $ do
          v <- jsm
          -- Store the value inside the window object
          object "window" # uq_lab := v
          up # putUplink 0
  addCompileTime engine t0

  t1 <- getCurrentTime
  send (cometDocument engine) (pack src)
  addSendTime engine t1

  t2 <- getCurrentTime
  -- There is *no* race condition in here. If no-one is listening,
  -- then the numbered event gets queued up.
  _ <- getUplink up
  addWaitTime engine t2
  return $ object "window" ! uq_lab

-- -----------------------------------------------------------------------
-- Default Server Instance
-- -----------------------------------------------------------------------

-- | A comet application takes the engine/document we are currently communicating
--   with and delivers the IO action to be executed as server application.
type SunroofApp = SunroofEngine -> IO ()

-- | The 'SunroofServerOptions' specify the configuration of the
--   sunroof comet server infrastructure.
--
--   See 'sunroofServer' and 'SunroofServerOptions' for further information.
data SunroofServerOptions = SunroofServerOptions
  { cometPort :: Port
  -- ^ The port the server is reachable from.
  , cometResourceBaseDir :: FilePath
  -- ^ Will be used as base directory to search for all static files.
  -- Make this path absolute to run the server from anywhere.
  , cometIndexFile :: FilePath
  -- ^ The file to be used as index file (or landing page).
  --   This path is given relative to the 'cometResourceBaseDir'.
  , cometPolicy :: Policy
  -- ^ The default policy is to allow the @css@, @img@ and @js@
  -- folders to be used by the server, as well as the noDots policy.
  --  This policy can be overwritten to allow delivery of other files.
  , cometOptions :: Options
  -- ^ Provides the kansas comet options to use.
  --   Default options are provided with the 'Data.Default.def' instance.
  , sunroofVerbose :: Int
  -- ^ @0@ for none, @1@ for initializations,
  --   @2@ for commands done and @3@ for a complete log.
  , sunroofCompilerOpts :: CompilerOpts
  -- ^ The set of options to configure the Sunroof compiler.
  --   Default options are provided with the 'Data.Default.def' instance.
  }

-- | Sets up a comet server ready to use with sunroof.
--
--   @sunroofServer opts app@:
--   The @opts@ give various configuration for the comet server.
--   See 'SunroofServerOptions' for further information on this.
--   The application to run is given by @app@. It takes the current
--   engine/document as parameter. The document is needed for calls to 'syncJS',
--   'asyncJS' and 'rsyncJS'.
--
--   The server provides the kansas comet Javascript on the path
--   @js/kansas-comet.js@.
--
--   Since @kansas-comet.js@ is a JQuery plugin you have to also
--   load a decent version of @jquery.js@ (or @jquery.min.js@)
--   and also @jquery-json.js@. They are available at:
--
--    * <http://jquery.com/>
--
--    * <https://code.google.com/p/jquery-json/>
--
--   For the index file to setup the communication correctly with the comet
--   server it has to load the @kansas-comet.js@ after the JQuery code
--   inside the @head@ (assuming you placed the JQuery code under @js/@):
--
-- >   <script type="text/javascript" src="js/jquery.js"></script>
-- >   <script type="text/javascript" src="js/jquery-json.js"></script>
-- >   <script type="text/javascript" src="js/kansas-comet.js"></script>
--
--   It also has to execute the following Javascript at the end of the
--   index file to initialize the communication:
--
-- >   <script type="text/javascript">
-- >     $(document).ready(function() {
-- >       $.kc.connect("/ajax");
-- >     });
-- >   </script>
--
--   The string @/ajax@ has to be set to whatever the comet prefix
--   in the 'Options' provided by the 'SunroofServerOptions' is.
--   These snippits will work for the 'def' instance.
--
--   Additional debug information can be displayed in the browser when
--   adding the following element to the index file:
--
-- >   <div id="debug-log"></div>
--
--   Look into the example folder to see all of this in action.
sunroofServer :: SunroofServerOptions -> SunroofApp -> IO ()
sunroofServer opts cometApp = do
  let warpSettings = setPort (cometPort opts) (SC.settings def)
  -- Be quiet scotty! ... and beam me up!
  let scottyOptions = def { SC.verbose = 0
                          , SC.settings = warpSettings }
  SC.scottyOpts scottyOptions $ do
    kcomet <- liftIO kCometPlugin
    let rootFile = cometResourceBaseDir opts </> cometIndexFile opts
    let custom_policy = cometPolicy opts
    let pol = only [("", rootFile)
                   ,("js/kansas-comet.js", kcomet)]
              <|> (custom_policy
                   >-> addBase (cometResourceBaseDir opts))
    SC.middleware $ staticPolicy pol
    connect (cometOptions opts) $ wrapDocument opts cometApp

-- | Wrap the document into the sunroof engine.
wrapDocument :: SunroofServerOptions -> SunroofApp -> (Document -> IO ())
wrapDocument opts cometApp doc = do
        uqVar <- atomically $ newTVar 0
        cometApp $ SunroofEngine
                               { cometDocument = doc
                               , uVar = uqVar
                               , engineVerbose = sunroofVerbose opts
                               , compilerOpts = sunroofCompilerOpts opts
                               , timings = Nothing
                               }

-- | Default options to use for the sunroof comet server.
--
--   [@cometPort@] Default port is @3000@.
--
--   [@cometResourceBaseDir@] Default resource location is @"."@.
--
--   [@cometIndexFile@] Default index file is @"index.html"@.
--
--   [@cometOptions@] Uses the server path @/ajax@ for the
--     comet JSON communication. Sets verbosity to @0@ (quiet).
--
--   [@sunroofVerbose@] Is set to @0@ (quiet).
--
defaultServerOpts :: SunroofServerOptions
defaultServerOpts = SunroofServerOptions
  { cometPort = 3000
  , cometResourceBaseDir = "."
  , cometIndexFile = "index.html"
  , cometPolicy = defaultPolicy
  , cometOptions = def { KC.prefix = "/ajax", KC.verbose = 0 }
  , sunroofVerbose = 0
  , sunroofCompilerOpts = def
  }

defaultPolicy :: Policy
defaultPolicy = noDots >-> (hasPrefix "css/" <|>
                            hasPrefix "js/"  <|>
                            hasPrefix "img/")

-- | The 'defaultServerOpts'.
instance Default SunroofServerOptions where
  def = defaultServerOpts

-- -------------------------------------------------------------
-- Downlink API
-- -------------------------------------------------------------

-- | 'Downlink's are an abstraction provided for sending
--   Javascript data from the server to the website.
--   The type parameter describes the elements
--   that are transmited through the downlink.
data Downlink a = Downlink SunroofEngine (JSChan a)

-- | Create a new downlink.
newDownlink :: forall a . (SunroofArgument a)
            => SunroofEngine -> IO (Downlink a)
newDownlink eng = do
  chan <- rsyncJS eng (newChan :: JSA (JSChan a))
  return $ Downlink eng chan

-- | Send data to the website.
putDownlink :: (SunroofArgument a)
            => Downlink a -> JSA a -> IO ()
putDownlink (Downlink eng chan) val = asyncJS eng $ do
  v <- val
  writeChan v chan

-- | Request data in the downlink. This may block until
--   data is available.
getDownlink :: (SunroofArgument a)
            => Downlink a -> JSB a
getDownlink (Downlink _eng chan) = readChan chan

-- -------------------------------------------------------------
-- Uplink API
-- -------------------------------------------------------------

-- | 'Uplink's are an abstraction provided for sending
--   Javascript data from the website back to the server.
--   Only data that can be translated back to a Haskell
--   value can be sent back.
--   The type parameter describes the elements
--   that are transmited through the uplink.
data Uplink a = Uplink SunroofEngine Uniq

-- | Create a new uplink.
newUplink :: SunroofEngine -> IO (Uplink a)
newUplink eng = do
  u <- docUniq eng
  return $ Uplink eng u

-- | Send Javascript data back to the server.
putUplink :: (SunroofArgument a) => a -> Uplink a -> JS t ()
putUplink a (Uplink _ u) =
        do o :: JSArgs a <- toJSArgs a
           kc_reply (js u) o

-- | Request data in the uplink. This may block until
--   data is available.
getUplink :: forall a . (SunroofResult a) => Uplink a -> IO (ResultOf a)
getUplink (Uplink eng u) = do
  val <- KC.getReply (cometDocument eng) u
  -- TODO: make this throw an exception if it goes wrong (I supose error does this already)
  return $ jsonToValue (Proxy :: Proxy (JSArgs a)) val
{-
  case val of
    (Array ss) -> return $ jsonToValue' (Proxy :: Proxy a) $ V.toList ss
    _ -> error $ "getUplink: expecting Array, found " ++ show val
-}
-- -------------------------------------------------------------
-- Comet Javascript API
-- -------------------------------------------------------------

-- | Binding for the Javascript function to send replies to the
--   server.
kc_reply :: (Sunroof a) => JSNumber -> a -> JS t ()
kc_reply n a = fun "$.kc.reply" `apply` (n,a)

-- -----------------------------------------------------------------------
-- JSON Value to Haskell/Sunroof conversion
-- -----------------------------------------------------------------------

-- | Provides correspondant Haskell types for certain Sunroof types.
class (SunroofArgument a) => SunroofResult a where
  -- | The Haskell value type associated with this 'Sunroof' type.
  type ResultOf a
  -- | Converts the given JSON value to the corresponding
  --   Haskell value. A error is thrown if the JSON value can
  --   not be converted.
  jsonToValue :: Proxy a -> Value -> ResultOf a

  jsonToValue' :: Proxy a -> [Value] -> ResultOf a
  jsonToValue' _ [s] = jsonToValue (Proxy :: Proxy a) s
  jsonToValue' _ ss  = error $ "jsonToValue': JSON value is not a single element array : " ++ show ss

-- | @null@ can be translated to @()@.
instance SunroofResult () where
  type ResultOf () = ()
  jsonToValue _ (Null) = ()
  jsonToValue _ v = error $ "jsonToValue: JSON value is not unit: " ++ show v

  jsonToValue' _ [] = ()
  jsonToValue' _ [Null] = ()    -- not quite right yet
  jsonToValue' _ ss  = error $ "jsonToValue': JSON value is not a empty array : " ++ show ss


-- | 'JSBool' can be translated to 'Bool'.
instance SunroofResult JSBool where
  type ResultOf JSBool = Bool
  jsonToValue _ (Bool b) = b
  jsonToValue _ v = error $ "jsonToValue: JSON value is not a boolean: " ++ show v

-- | 'JSNumber' can be translated to 'Double'.
instance SunroofResult JSNumber where
  type ResultOf JSNumber = Double
  jsonToValue _ (Number scientific) = toRealFloat scientific
  jsonToValue _ v = error $ "jsonToValue: JSON value is not a number: " ++ show v

-- | 'JSString' can be translated to 'String'.
instance SunroofResult JSString where
  type ResultOf JSString = String
  jsonToValue _ (String s) = unpack s
  jsonToValue _ v = error $ "jsonToValue: JSON value is not a string: " ++ show v

-- | 'JSArray' can be translated to a list of the 'ResultOf' the values.
instance forall a . (Sunroof a, SunroofResult a) => SunroofResult (JSArray a) where
  type ResultOf (JSArray a) = [ResultOf a]
  jsonToValue _ (Array ss) = map (jsonToValue (Proxy :: Proxy a)) $ V.toList ss
  jsonToValue _ v = error $ "jsonToValue: JSON value is not an array : " ++ show v

-- ResultOf a ~ ResultOf (JSArgs a))
instance forall a . SunroofResult a => SunroofResult (JSArgs a) where
  type ResultOf (JSArgs a) = ResultOf a
  jsonToValue _ (Array ss) = jsonToValue' (Proxy :: Proxy a) $ V.toList ss
  jsonToValue _ v = error $ "jsonToValue: JSON value is not an array : " ++ show v

instance forall a b . (Sunroof a, SunroofResult a, Sunroof b, SunroofResult b) => SunroofResult (a,b) where
  type ResultOf (a,b) = (ResultOf a,ResultOf b)
  jsonToValue _ (Array ss) = case V.toList ss of
          [x1,x2] -> (jsonToValue (Proxy :: Proxy a) x1, jsonToValue (Proxy :: Proxy b) x2)
          xs -> error $ "sonToValue: JSON value is not a 2-tuple : " ++ show xs
  jsonToValue _ v = error $ "jsonToValue: JSON value is not an array : " ++ show v

-- | Converts a JSON value to a Sunroof Javascript expression.
jsonToJS :: Value -> Expr
jsonToJS (Bool b)       = unbox $ js b
jsonToJS (Number scientific) = unbox $ js scientific
jsonToJS (String s)     = unbox $ js $ unpack s
jsonToJS (Null)         = unbox $ nullJS
jsonToJS (Array arr)    = jsonArrayToJS arr
jsonToJS (Object obj)   = jsonObjectToJS obj

-- | Converts a JSON object to a Sunroof expression.
jsonObjectToJS :: Object -> Expr
jsonObjectToJS obj = literal $
  let literalMap = M.toList $ fmap (show . jsonToJS) obj
      convertKey k = "\"" ++ unpack k ++ "\""
      keyValues = fmap (\(k,v) -> convertKey k ++ ":" ++ v) literalMap
  in "{" ++ intercalate "," keyValues ++ "}"

-- | Converts a JSON array to a Sunroof expression.
jsonArrayToJS :: Array -> Expr
jsonArrayToJS arr = literal $
  "(new Array(" ++ (intercalate "," $ V.toList $ fmap (show . jsonToJS) arr) ++ "))"

{- Orphans:
instance SunroofValue Value where
  type ValueOf Value = JSObject
  js = box . jsonToJS

instance SunroofValue Text where
  type ValueOf Text = JSString
  js = string . unpack
-}

-- -------------------------------------------------------------
-- Debugging
-- -------------------------------------------------------------

-- | Setup a 'SunroofEngine' for debugging.
debugSunroofEngine :: IO SunroofEngine
debugSunroofEngine = do
  doc <- KC.debugDocument
  uqVar <- atomically $ newTVar 0
  return $ SunroofEngine doc uqVar 3 def Nothing

-- | Timings for communication and compilation.
data Timings a = Timings
        { compileTime :: !a -- ^ How long spent compiling.
        , sendTime    :: !a -- ^ How long spent sending.
        , waitTime    :: !a -- ^ How long spent waiting for a response.
        }
        deriving Show

-- | Apply a function by applying it to each timing.
instance Functor Timings where
  fmap f (Timings t1 t2 t3) = Timings (f t1) (f t2) (f t3)

-- | Combine timings by combining each single timing.
instance Semigroup a => Semigroup (Timings a) where
  (Timings t1 t2 t3) <> (Timings u1 u2 u3)  = Timings (t1<>u1) (t2<>u2) (t3<>u3)

-- | Create timings in the 'SunroofEngine'.
newTimings :: SunroofEngine -> IO SunroofEngine
newTimings e = do
        v <- atomically $ newTVar $ Timings 0 0 0
        return $ e { timings = Just v }

-- | Reset all timings.
resetTimings :: SunroofEngine -> IO ()
resetTimings (SunroofEngine { timings = Nothing }) = return ()
resetTimings (SunroofEngine { timings = Just t }) = atomically $ writeTVar t $ Timings 0 0 0

-- | Get timings from the 'SunroofEngine'.
getTimings :: SunroofEngine -> IO (Timings NominalDiffTime)
getTimings (SunroofEngine { timings = Nothing }) = return $ Timings 0 0 0
getTimings (SunroofEngine { timings = Just t }) = atomically $ readTVar t

-- | Add a timing for compilation.
addCompileTime :: SunroofEngine -> UTCTime -> IO ()
addCompileTime (SunroofEngine { timings = Nothing }) _start = return ()
addCompileTime (SunroofEngine { timings = Just t }) start = do
        end <- getCurrentTime
        atomically $ modifyTVar t $ \ ts -> ts { compileTime = compileTime ts + diffUTCTime end start}
        return ()

-- | Add a timing for sending.
addSendTime :: SunroofEngine -> UTCTime -> IO ()
addSendTime (SunroofEngine { timings = Nothing }) _start = return ()
addSendTime (SunroofEngine { timings = Just t }) start = do
        end <- getCurrentTime
        atomically $ modifyTVar t $ \ ts -> ts { sendTime = sendTime ts + diffUTCTime end start}
        return ()

-- | Add a timing for waiting for a response.
addWaitTime :: SunroofEngine -> UTCTime -> IO ()
addWaitTime (SunroofEngine { timings = Nothing }) _start = return ()
addWaitTime (SunroofEngine { timings = Just t }) start = do
        end <- getCurrentTime
        atomically $ modifyTVar t $ \ ts -> ts { waitTime = waitTime ts + diffUTCTime end start}
        return ()
