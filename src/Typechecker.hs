{-# LANGUAGE LambdaCase, TemplateHaskell #-}
{-# OPTIONS_GHC -Wno-incomplete-uni-patterns #-}
{-# LANGUAGE TupleSections #-}
module Typechecker where

import Parser (TopLevel(..), Node(..), AtomType(..))
import Control.Lens
import Control.Monad.State
import qualified Data.HashMap.Strict as H
import qualified Data.HashSet as S

maybeToEither :: a -> Maybe b -> Either a b
maybeToEither _ (Just b) = Right b
maybeToEither a Nothing  = Left a

update :: MonadState a m => (a -> a) -> m a
update f = modify f >> get

type Identificator = (String, Int)

data TypeError = TypeError -- ...

data MonoType =
    Variable    { varIdentifier :: Identificator , vConstraints :: S.HashSet String                }
  | Constructor { constructor   :: Node          , typeArgs     :: [MonoType]                      }
  | Function    { fromClass     :: Bool          , takesType    :: MonoType , retsType :: MonoType }
  | BuiltinNat | BuiltinReal | BuiltinChar | BuiltinString
  | Bottom -- just for convencience
  deriving (Eq)

-- (Poly)Type
data Type = Scheme { bounds :: H.HashMap String (S.HashSet String), monoBounded :: MonoType }

newtype Subs = Subs { _typeMap :: H.HashMap String MonoType }

data TheContext =
  TheContext {
    _functionContext :: H.HashMap String Type,
    _typeContext     :: H.HashMap String [Type],
    _classContext    :: H.HashMap String (H.HashMap String (S.HashSet (H.HashMap String Type))),
    _typeGenerator   :: MonoType
  }
makeLenses ''TheContext

typeMap :: Subs -> MonoType -> MonoType
typeMap = undefined

polyMap :: Subs -> Type -> Type
polyMap = undefined

generateFrom :: MonoType -> MonoType
generateFrom (Variable (n, i) c) = Variable (n, i + 1) c
generateFrom _                   = undefined

instance Semigroup Subs where
  (<>) = compose

instance Monoid Subs where
  mempty = Subs H.empty

compose :: Subs -> Subs -> Subs
compose = undefined

typeExprToType :: H.HashMap String [Node]  -> Node -> Type
typeExprToType = undefined

freeInCtx :: TheContext -> H.HashMap String (S.HashSet String)
freeInCtx = undefined

unify :: MonoType -> MonoType -> StateT TheContext (Either TypeError) Subs
unify = undefined

instantiate :: Type -> StateT TheContext (Either TypeError) MonoType
instantiate = undefined

algoW :: Node -> StateT TheContext (Either TypeError) (Subs, MonoType)
algoW (Atom name' type' _) =
  (mempty, ) <$> case type' of
    Identifier -> getFunc
    Operator   -> getFunc
    Nat        -> return BuiltinNat
    Real'      -> return BuiltinReal 
    Char'      -> return BuiltinChar 
    String'    -> return BuiltinString
    _          -> undefined
  where getFunc = gets _functionContext
                  >>= lift . maybeToEither TypeError . H.lookup name'
                  >>= instantiate

algoW (Expression (e:es)) = do
  (sF, tF) <- algoW e
  modify $ functionContext `over` H.map (polyMap sF)
  (sAs, tAs) <- foldM (\(sA, tAs) eArg -> do {
      (sAn, tAn) <- algoW eArg;
      modify $ functionContext `over` H.map (polyMap sAn);
      return (sA `compose` sAn, tAn : tAs)
    }) (mempty, []) (reverse es)
  beta <- _typeGenerator <$> update (typeGenerator `over` generateFrom)
  sExpr <- unify (typeMap sAs tF) (Function False (foldl1 (Function False) tAs) beta)
  return (sExpr `compose` sAs `compose` sF, typeMap sExpr beta)

algoW (BinaryExpr lExpr op' rExpr) = algoW $ Expression [op', lExpr, rExpr]

algoW (LocalBind locName' localBind') = do
  (sB, tB) <- algoW localBind'
  ctx <- update (functionContext `over` H.map (polyMap sB))
  modify $ functionContext `over` H.insert (name locName') (Scheme (freeInCtx ctx) tB)
  return (sB, typeMap sB tB)

algoW (TypeAssertion {}) = undefined

algoW _ = undefined

typeOfExpr :: Node -> StateT TheContext (Either TypeError) MonoType
typeOfExpr = fmap snd . algoW

check :: TopLevel -> StateT TheContext (Either TypeError) TopLevel
check impl@(Implementation fName fArgs bodyL) = do
  ctx <- get
  implType <- foldl1 (Function False) <$> mapM genBeta (fArgs ++ [fName])
  lastSub <- foldM (\s b -> mappend s . fst <$> algoW b) mempty bodyL
  free <- gets freeInCtx
  put ctx
  fSub <- case H.lookup (name fName) (_functionContext ctx) of
    Just f -> instantiate f >>= unify (typeMap lastSub implType)
    Nothing -> return lastSub
  modify $ functionContext `over` H.insert (name fName) (Scheme free $ typeMap fSub implType)
  return impl
  where
    genBeta :: Node -> StateT TheContext (Either TypeError) MonoType
    genBeta n = do
      beta <- _typeGenerator <$> update (typeGenerator `over` generateFrom)
      modify $ functionContext `over` H.insert (name n) (Scheme H.empty beta)
      return beta

check decl@(Declaration dName cnstr dType) = do
  modify $ functionContext `over` H.insert (name dName) (typeExprToType cnstr dType)
  return decl

check _ = undefined

checker :: [TopLevel] -> StateT TheContext (Either TypeError) [TopLevel]
checker = traverse check . filter (\case { Infix -> False; _ -> True })
