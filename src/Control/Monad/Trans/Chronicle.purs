module Control.Monad.Trans.Chronicle where

import Prelude

import Control.Alt (class Alt)
import Control.Alternative (class Alternative)
import Control.Apply (lift2)
import Control.Monad.Error.Class (class MonadError, class MonadThrow, catchError, throwError)
import Control.Monad.Reader (class MonadAsk, class MonadReader, ask, local)
import Control.Monad.State (class MonadState, state)
import Control.Monad.Trans.Class (class MonadTrans, lift)
import Control.Monad.Writer (class MonadTell, class MonadWriter, listen, pass, tell)
import Control.MonadPlus (class MonadPlus)
import Control.MonadZero (class MonadZero)
import Control.Plus (class Plus)
import Data.Bifunctor (bimap)
import Data.Either (Either(..))
import Data.Identity (Identity)
import Data.Newtype (class Newtype, unwrap, wrap)
import Data.These (These(..), these)
import Data.Tuple (Tuple(..))
import Effect.Class (class MonadEffect, liftEffect)

type Chronicle c = ChronicleT c Identity

mkChronicle :: forall c a. These c a -> Chronicle c a
mkChronicle = wrap <<< wrap

runChronicle :: forall c a. Chronicle c a -> These c a
runChronicle = unwrap <<< unwrap

dictate :: forall c m. Semigroup c => Monad m => c -> ChronicleT c m Unit
dictate c = ChronicleT $ pure (Both c unit)

confess :: forall c m a. Semigroup c => Monad m => c -> ChronicleT c m a
confess c = ChronicleT $ pure (This c)

memento :: forall c m a. Semigroup c => Monad m => ChronicleT c m a -> ChronicleT c m (Either c a)
memento m = ChronicleT do
  cx <- unwrap m
  pure $ case cx of
      This a -> That (Left a)
      That x -> That (Right x)
      Both a x -> Both a (Right x)

absolve :: forall c m a. Semigroup c => Monad m => a -> ChronicleT c m a -> ChronicleT c m a
absolve x m = ChronicleT do 
  cy <- unwrap m
  pure $ case cy of
      This _ -> That x
      That y -> That y
      Both _ y -> That y

condemn :: forall c m a. Semigroup c => Monad m => ChronicleT c m a -> ChronicleT c m a
condemn (ChronicleT m) = ChronicleT do 
  m' <- m
  pure $ case m' of
      This x -> This x
      That y -> That y
      Both x _ -> This x

retcon :: forall c m a. Semigroup c => Monad m => (c -> c) -> ChronicleT c m a -> ChronicleT c m a
retcon f m = ChronicleT $ bimap f identity <$> unwrap m

newtype ChronicleT c m a = ChronicleT (m (These c a))

derive instance newtypeChronicleT :: Newtype (ChronicleT c m a) _

instance functorChronicleT :: Functor m => Functor (ChronicleT c m) where
  map f (ChronicleT c) = ChronicleT (map f <$> c)

instance applyChronicleT :: (Semigroup c, Apply m) => Apply (ChronicleT c m) where
  apply (ChronicleT f) (ChronicleT x) = ChronicleT (lift2 (<*>) f x)

instance applicativeChronicleT :: (Semigroup c, Applicative m) => Applicative (ChronicleT c m) where
  pure = ChronicleT <<< pure <<< pure

instance bindChronicleT :: (Semigroup c, Applicative m, Bind m) => Bind (ChronicleT c m) where
  bind m k = ChronicleT $ do
    cx <- unwrap m
    case cx of
      This a -> pure (This a)
      That x -> unwrap (k x)
      Both a x -> do
        cy <- unwrap (k x)
        pure $ case cy of
          This b -> This (a <> b)
          That y -> Both a y
          Both b y -> Both (a <> b) y

instance monadChronicleT :: (Semigroup c, Monad m) => Monad (ChronicleT c m)

instance altChronicleT :: (Semigroup c, Monad m) => Alt (ChronicleT c m) where
  alt x y = do
    x' <- memento x
    case x' of
      Left _ -> y
      Right r -> pure r

instance plusChronicleT :: (Monoid c, Monad m) => Plus (ChronicleT c m) where
  empty = confess mempty    

instance alternativeChronicleT :: (Monoid c, Monad m) => Alternative (ChronicleT c m)
instance monadZeroChronicleT :: (Monoid c, Monad m) => MonadZero (ChronicleT c m)
instance monadPlusChronicleT :: (Monoid c, Monad m) => MonadPlus (ChronicleT c m)

instance monadTransChronicleT :: Semigroup c => MonadTrans (ChronicleT c) where
  lift m = ChronicleT (That <$> m)

instance monadEffectChronicleT :: (Semigroup c, MonadEffect m) => MonadEffect (ChronicleT c m) where
  liftEffect = lift <<< liftEffect

instance monadThrowChronicleT :: (Semigroup c, MonadThrow e m) => MonadThrow e (ChronicleT c m) where
  throwError = lift <<< throwError

instance monadErrorChronicleT :: (Semigroup c, MonadError e m) => MonadError e (ChronicleT c m) where
  catchError (ChronicleT m) c = ChronicleT $ catchError m (unwrap <<< c)

instance monadAskChronicleT :: (Semigroup c, MonadAsk r m) => MonadAsk r (ChronicleT c m) where
  ask = lift ask

instance monadReaderChronicleT :: (Semigroup c, MonadReader r m) => MonadReader r (ChronicleT c m) where
  local f (ChronicleT m) = ChronicleT $ local f m

instance monadStateChronicleT :: (Semigroup c, MonadState s m) => MonadState s (ChronicleT c m) where
  state = lift <<< state

instance monadTellChronicleT :: (Semigroup c, MonadTell w m) => MonadTell w (ChronicleT c m) where
  tell = lift <<< tell

instance monadWriterChronicleT :: (Semigroup c, MonadWriter w m) => MonadWriter w (ChronicleT c m) where
  listen (ChronicleT m) = ChronicleT $ do
    Tuple m' w <- listen m
    pure $ case m' of
      This c -> This c
      That x -> That (Tuple x w)
      Both c x -> Both c (Tuple x w)
  pass (ChronicleT m) = ChronicleT $ do
    pass $ these (\c -> (Tuple (This c) identity))  (\(Tuple x f) -> (Tuple (That x) f)) (\c (Tuple x f) -> (Tuple (Both c x) f)) <$> m