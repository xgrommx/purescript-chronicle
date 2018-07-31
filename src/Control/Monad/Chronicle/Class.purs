module Control.Monad.Chronicle.Class where

import Prelude

import Control.Monad.Trans.Class (lift)
import Control.Monad.Except (ExceptT(..))
import Control.Monad.Maybe.Trans (MaybeT(..))
import Control.Monad.RWS (RWSResult(..), RWST(..))
import Control.Monad.Reader (ReaderT(..))
import Control.Monad.State (StateT)
import Control.Monad.Trans.Chronicle as Chronicle
import Control.Monad.Writer (WriterT(..))
import Data.Bifunctor (bimap)
import Data.Either (Either(..), either)
import Data.Maybe (Maybe(..))
import Data.Newtype (unwrap, wrap)
import Data.These (These(..))
import Data.Tuple (Tuple(..))

class Monad m <= MonadChronicle c m | m -> c where
  dictate :: c -> m Unit
  confess :: forall a. c -> m a
  memento :: forall a. m a -> m (Either c a)
  absolve :: forall a. a -> m a -> m a
  condemn :: forall a. m a -> m a
  retcon :: forall a. (c -> c) -> m a -> m a
  chronicle :: forall a. These c a -> m a

instance monadChronicleMaybeT :: MonadChronicle c m => MonadChronicle c (MaybeT m) where
  dictate = lift <<< dictate
  confess = lift <<< confess
  memento (MaybeT m) = MaybeT $ either (Just <<< Left) (Right <$> _) <$> memento m
  absolve x (MaybeT m) = MaybeT $ absolve (Just x) m
  condemn (MaybeT m) = MaybeT $ condemn m
  retcon f (MaybeT m) = MaybeT $ retcon f m
  chronicle = lift <<< chronicle

instance monadChronicleThese :: Semigroup c => MonadChronicle c (These c) where
  dictate c = Both c unit
  confess c = This c
  memento (This c) = That (Left c)
  memento m = bimap identity Right m
  absolve x (This _) = That x
  absolve _ (That x) = That x
  absolve _ (Both _ x) = That x
  condemn (Both c _) = This c
  condemn m = m
  retcon f = bimap f identity
  chronicle = identity

instance monadChronicleExceptT :: MonadChronicle c m => MonadChronicle c (ExceptT e m) where
  dictate = lift <<< dictate
  confess = lift <<< confess
  memento (ExceptT m) = ExceptT $ either (Right <<< Left) (Right <$> _) <$> memento m
  absolve x (ExceptT m) = ExceptT $ absolve (Right x) m
  condemn (ExceptT m) = ExceptT $ condemn m
  retcon f (ExceptT m) = ExceptT $ retcon f m
  chronicle = lift <<< chronicle

instance monadChronicleChronicleT :: (Semigroup c, Monad m) => MonadChronicle c (Chronicle.ChronicleT c m) where
  dictate c = Chronicle.dictate c
  confess c = Chronicle.confess c
  memento m = Chronicle.memento m
  absolve x m = Chronicle.absolve x m
  condemn m = Chronicle.condemn m
  retcon f m = Chronicle.retcon f m
  chronicle = Chronicle.ChronicleT <<< pure

instance monadChronicleReaderT :: MonadChronicle c m => MonadChronicle c (ReaderT r m) where
  dictate = lift <<< dictate
  confess = lift <<< confess
  memento (ReaderT m) = ReaderT $ memento <<< m
  absolve x (ReaderT m) = ReaderT $ absolve x <<< m
  condemn (ReaderT m) = ReaderT $ condemn <<< m
  retcon f (ReaderT m) = ReaderT $ retcon f <<< m
  chronicle = lift <<< chronicle

instance monadChronicleStateT :: MonadChronicle c m => MonadChronicle c (StateT s m) where
  dictate = lift <<< dictate
  confess = lift <<< confess
  memento m = wrap $ \s -> do
      either (\c -> Tuple (Left c) s) (\(Tuple a s') -> (Tuple (Right a) s')) <$> memento (unwrap m s)
  absolve x m = wrap $ \s -> absolve (Tuple x s) $ (unwrap m) s
  condemn m = wrap $ condemn <<< unwrap m
  retcon f m = wrap $ retcon f <<< unwrap m
  chronicle = lift <<< chronicle

instance monadChronicleWriterT :: (Monoid w, MonadChronicle c m) => MonadChronicle c (WriterT w m) where
  dictate = lift <<< dictate
  confess = lift <<< confess
  memento (WriterT m) = WriterT $ 
      either (\c -> (Tuple (Left c) mempty)) (\(Tuple a w) -> (Tuple (Right a) w)) <$> memento m
  absolve x (WriterT m) = WriterT $ absolve (Tuple x mempty) m
  condemn (WriterT m) = WriterT $ condemn m
  retcon f (WriterT m) = WriterT $ retcon f m
  chronicle = lift <<< chronicle

instance monadChronicleRWST :: (Monoid w, MonadChronicle c m) => MonadChronicle c (RWST r w s m) where
  dictate = lift <<< dictate
  confess = lift <<< confess
  memento (RWST m) = RWST $ \r s ->
      either (\c -> (RWSResult s (Left c) mempty)) (\(RWSResult s' a w) -> (RWSResult s' (Right a) w)) <$> memento (m r s)
  absolve x (RWST m) = RWST $ \r s -> absolve (RWSResult s x mempty) $ m r s
  condemn (RWST m) = RWST $ \r s -> condemn $ m r s
  retcon f (RWST m) = RWST $ \r s -> retcon f $ m r s
  chronicle = lift <<< chronicle