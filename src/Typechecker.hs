{-# LANGUAGE LambdaCase, TemplateHaskell #-}
{-# OPTIONS_GHC -Wno-incomplete-uni-patterns #-}
{-# LANGUAGE TupleSections #-}
module Typechecker where

import Parser (TopLevel(..), Node(..), AtomType(..), MonoType(..), Identificator, TypeError(..))
import Data.Bool
import Data.Function
import Data.Functor
import Control.Arrow
import Control.Lens
import Control.Monad.State
import qualified Data.HashMap.Strict as H
import qualified Data.HashSet as S

-- Helpers

fst3 :: (a, b, c) -> a
snd3 :: (a, b, c) -> b
thrd :: (a, b, c) -> c

fst3 (a, _, _) = a
snd3 (_, b, _) = b
thrd (_, _, c) = c

maybeToEither :: a -> Maybe b -> Either a b
maybeToEither _ (Just b) = Right b
maybeToEither a Nothing  = Left a

update :: MonadState a m => (a -> a) -> m a
update f = modify f >> get

--

-- (Poly)Type
data Type = Scheme { bounds :: H.HashMap Identificator (S.HashSet String), monoBounded :: MonoType }

newtype Subs = Subs { _typeMap :: H.HashMap Identificator MonoType }

data TheContext =
  TheContext {
    _functionContext :: H.HashMap String Type,
    _typeContext     :: H.HashMap String [Type],
    _instanceContext :: H.HashMap String (S.HashSet String),
    _classContext    :: H.HashMap String (S.HashSet String),
    _typeGenerator   :: MonoType
  }
makeLenses ''TheContext

typeMap :: Subs -> MonoType -> MonoType
typeMap s t@(Variable v _) = H.findWithDefault t v (_typeMap s)
typeMap s (Function c tT rT) = let m = typeMap s tT
                                   m' = typeMap s rT
                             in Function c m m'
typeMap _ t                = t

singleMap :: MonoType -> MonoType -> Subs
singleMap (Variable n c) (Variable n' c') = Subs . H.singleton n $ Variable  n' (c `S.union` c')
singleMap (Variable n _) t                = Subs . H.singleton n $ t
singleMap _              _                = undefined

polyMap :: Subs -> Type -> Type
polyMap (Subs m) (Scheme bounds' monoBounded') = Scheme bounds' $ typeMap (Subs $ m `H.difference` bounds') monoBounded'

generateFrom :: MonoType -> MonoType
generateFrom (Variable (n, i) c) = Variable (n, i + 1) c
generateFrom _                   = undefined

instance Semigroup Subs where
  (<>) = compose

instance Monoid Subs where
  mempty = Subs H.empty

compose :: Subs -> Subs -> Subs
compose (Subs m1) (Subs m2) = Subs $ H.foldMapWithKey (\t t' m -> H.alter (\case {
      Nothing  -> Just t';
      Just t''@(Variable v'' _) -> Just $ H.findWithDefault t'' v'' m;
      Just t'' -> Just t''
    }) t m) m1 m2

typeExprToType :: H.HashMap String [Node] -> Node -> StateT TheContext (Either TypeError) Type
typeExprToType cnstraints typeExpr = do
  (tVars, monoExpr) <- toMono typeExpr
  return $ Scheme (H.mapKeys (, 0) (H.map (S.fromList . map name) cnstraints) `H.union` tVars) monoExpr
  where
    toMono :: Node -> StateT TheContext (Either TypeError) (H.HashMap Identificator (S.HashSet String), MonoType)
    toMono (Atom n _ _ _) = return (H.singleton (n, 0) S.empty, Variable (n, 0) S.empty)
    toMono (Expression tExpr) = foldl1 (\(v, m) (v', m') -> (v `H.union` v', Function False m m')) <$> mapM toMono tExpr
    toMono (ConcType i a) = do
      typeCtx <- gets _typeContext
      lift $ case H.lookup (name i) typeCtx of
        Just args' -> bool (Left TypeError) (Right ()) $ length a == length args'
        Nothing    -> Left TypeError
      mapM toMono a <&> second (Constructor i) . sequence
    toMono _ = undefined

constructorToType :: Node -> Type
constructorToType = undefined

freeInType :: Type -> H.HashMap Identificator (S.HashSet String)
freeInType (Scheme bounds' monoBounded') = freeInType' monoBounded' `H.difference` bounds'
  where
    freeInType' :: MonoType -> H.HashMap Identificator (S.HashSet String)
    freeInType' Bottom = undefined
    freeInType' (Variable n c) = H.singleton n c
    freeInType' (Function _ m1 m2) = freeInType' m1 `H.union` freeInType' m2
    freeInType' _                  = H.empty

freeInCtx :: TheContext -> H.HashMap Identificator (S.HashSet String)
freeInCtx (TheContext ctx _ _ _ _) = foldl (\s p -> s `H.union` freeInType p) H.empty ctx

unify :: MonoType -> MonoType -> StateT TheContext (Either TypeError) Subs
unify v@(Variable s c)    v'@(Variable s' c')
  | s == s'             = lift $ Right mempty
  | c `S.isSubsetOf` c' = lift $ Right $ singleMap v v'
  | otherwise           = lift $ Right $ singleMap v' v
unify v@(Variable _ c) t'@(Constructor i _) = do
  typeCtx <- gets _instanceContext
  lift $ case H.lookup (name i) typeCtx of
    Just c' -> bool (Left TypeError) (Right $ singleMap v t') $ c' `S.isSubsetOf` c
    Nothing -> Left TypeError
unify v@(Variable _ _)    t'
  | v `isIn` t' = lift $ Left TypeError
  | otherwise   = lift $ Right $ singleMap v t'
  where isIn v' (Function _ rT tT) = v' `isIn` rT || v' `isIn` tT
        isIn v' v''@(Variable _ _) = v' == v''
        isIn _  _                = False
unify t                 v'@(Variable _ _)      = unify v' t
unify (Constructor i _) (Constructor i' _) = lift $ bool (Left TypeError) (Right mempty) (i == i')
unify (Function _ tT rT)  (Function _ tT' rT') = unify tT tT' >>= \u -> compose u <$> (unify `on` typeMap u) rT rT'
unify _                 _                      = lift $ Left TypeError

instantiate :: Type -> StateT TheContext (Either TypeError) MonoType
instantiate (Scheme bounds' monoBounded')= do
  instMap <- H.foldlWithKey instanceMap (return $ typeMap mempty) bounds'
  return $ instMap monoBounded'
  where
    instanceMap :: StateT TheContext (Either TypeError) (MonoType -> MonoType) -> Identificator -> S.HashSet String -> StateT TheContext (Either TypeError) (MonoType -> MonoType)
    -- for some reason Haskell cannot infer this very easy to read, and easy to understand type
    instanceMap mmap k c = do
      map' <- mmap
      nBeta <- varIdentifier . _typeGenerator <$> update (typeGenerator `over` generateFrom)
      return $ (. map') $ typeMap $ singleMap (Variable k c) $ Variable nBeta c

algoW :: Node -> StateT TheContext (Either TypeError) (Subs, MonoType, Node)
algoW (Atom name' type' _ pos') =
  assoc . (mempty, ) <$> case type' of
    Identifier -> typeAndTyped <$> getFunc
    Operator   -> typeAndTyped <$> getFunc
    Nat        -> return $ typeAndTyped BuiltinNat
    Real'      -> return $ typeAndTyped BuiltinReal
    Char'      -> return $ typeAndTyped BuiltinChar
    String'    -> return $ typeAndTyped BuiltinString
    _          -> undefined
  where getFunc = gets _functionContext
                  >>= lift . maybeToEither TypeError . H.lookup name'
                  >>= instantiate
        assoc (a, (b, c)) = (a, b, c)
        typeAndTyped m = (m, Atom name' type' m pos')

algoW (Lambda args' expr') = do
  betas <- mapM addArg  args'
  (sE, tE, lT) <- algoW expr'
  return (sE, typeMap sE $ foldl1 (Function False) (betas ++ [tE]), lT)
  where
    addArg :: Node -> StateT TheContext (Either TypeError) MonoType
    addArg a = do
      beta <- _typeGenerator <$> update (typeGenerator `over` generateFrom)
      modify . (functionContext `over`) . H.insert (name a) . Scheme H.empty $ beta
      return beta

algoW (Expression (e:es)) = do
  (sF, tF, fT) <- algoW e
  modify $ functionContext `over` H.map (polyMap sF)
  (sAs, tAs, eT) <- foldM (\(sA, tAs, eTs) eArg -> do {
      (sAn, tAn, eTn) <- algoW eArg;
      modify $ functionContext `over` H.map (polyMap sAn);
      return (sA `compose` sAn, tAn : tAs, eTn : eTs)
    }) (mempty, [], []) (reverse es)
  beta <- _typeGenerator <$> update (typeGenerator `over` generateFrom)
  sExpr <- unify (typeMap sAs tF) (Function False (foldl1 (Function False) tAs) beta)
  return (sExpr `compose` sAs `compose` sF, typeMap sExpr beta, Expression $ fT:eT)

algoW (BinaryExpr lExpr op' rExpr) = algoW $ Expression [op', lExpr, rExpr]

algoW (LocalBind locName' localBind') = do
  (sB, tB, bT) <- algoW localBind'
  ctx <- update (functionContext `over` H.map (polyMap sB))
  modify $ functionContext `over` H.insert (name locName') (Scheme (freeInCtx ctx) tB)
  return (sB, tB, bT)

algoW (TypeAssertion e c t) = do
  (sE, tE, bT) <- algoW e
  tE' <- typeExprToType c t >>= instantiate
  sE' <- unify tE tE'
  return (sE' `compose` sE, typeMap sE' tE', bT)

algoW (ConcType {}) = undefined

algoW _ = undefined

typeOfExpr :: Node -> StateT TheContext (Either TypeError) MonoType
typeOfExpr = fmap snd3 . algoW

check :: TopLevel -> StateT TheContext (Either TypeError) [TopLevel]

check (Implementation fName fArgs bodyL) = do
  ctx <- get
  implType <- foldl1 (Function False) <$> mapM genBeta (fArgs ++ [fName])
  (lastSub, typedBody) <- foldM (\(s, b') b -> ((s <>) *** (: b')) . (fst3 &&& thrd) <$> algoW b) (mempty, []) $ reverse bodyL
  free <- gets freeInCtx
  put ctx
  fSub <- case H.lookup (name fName) (_functionContext ctx) of
    Just f -> instantiate f >>= unify (typeMap lastSub implType)
    --                          ^~~~ should be an equality function instead
    Nothing -> return lastSub
  modify $ functionContext `over` H.insert (name fName) (Scheme free $ typeMap fSub implType)
  return [Implementation fName fArgs typedBody]
  where
    genBeta :: Node -> StateT TheContext (Either TypeError) MonoType
    genBeta n = do
      beta <- _typeGenerator <$> update (typeGenerator `over` generateFrom)
      modify $ functionContext `over` H.insert (name n) (Scheme H.empty beta)
      return beta

check decl@(Declaration dName cnstr dType) = do
  declarationType <- typeExprToType cnstr dType
  modify $ functionContext `over` H.insert  (name dName) declarationType
  return [decl]

check dataD@(Data typeName' implementations') = do
  modify $ instanceContext `over` H.insert (name typeName') S.empty
  mapM_ (\conc@(ConcType n _) -> modify $ functionContext `over` H.insert (name n) (constructorToType conc)) implementations'
  return [dataD]

check (Instance instancing' instanced' implementations') = do
  ctx <- get
  lift $ case H.lookup (name instancing') $ _classContext ctx of
    Just class' -> bool (Left TypeError) (Right ()) $ class' == H.keysSet implementations'
    Nothing     -> Left TypeError
  impls <- mapM check (concatMap snd $ H.toList implementations') >>= mapM mangle . concat
  put ctx
  modify $ instanceContext `over` H.alter (Just . \case { Just s -> S.insert (name instancing') s; Nothing -> S.singleton (name instancing');} ) (name instanced')
  return impls
  where
    unwrapJust (Just x) = x
    unwrapJust Nothing  = undefined
    renameWith (Atom n k t p) n' = Atom (n++n') k t p
    renameWith _              _  = undefined
    stringify (Variable (s, n)  _) = s ++ show n
    stringify (Constructor i n)    = name i ++ foldr (\n' s' -> (s' ++) . stringify $ n') "" n
    stringify (Function _ t r)     = stringify t ++ '-' : stringify r
    stringify rest = case rest of
      BuiltinNat -> "Nat"
      BuiltinChar -> "Char"
      BuiltinReal -> "Real"
      BuiltinString -> "String"
      Bottom -> undefined
    mangle :: TopLevel -> StateT TheContext (Either TypeError) TopLevel
    mangle (Implementation fName' fArgs' bodyT') = do
      (Scheme _ tFunc) <- gets $ unwrapJust . H.lookup (name fName') . _functionContext
      return $ Implementation (renameWith fName' $ stringify tFunc) fArgs' bodyT'
    mangle _ = undefined


check (Class className' declarations') = do
  classCtx <- gets _classContext
  case H.lookup (name className') classCtx of
    Just _ -> lift $ Left TypeError
    Nothing -> modify $ classContext `over` H.insert (name className') (H.keysSet declarations')
  mapM_ check declarations'
  return []

check Infix = undefined

checker :: [TopLevel] -> StateT TheContext (Either TypeError) [TopLevel]
checker = fmap concat . traverse check . filter (\case { Infix -> False; _ -> True })
