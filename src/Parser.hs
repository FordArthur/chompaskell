{-# OPTIONS_GHC -Wno-incomplete-uni-patterns #-}
module Parser where

import Data.Functor ((<&>))
import Control.Arrow
import Text.Parsec
import Text.Parsec.Pos
import qualified Data.HashMap.Strict as H
import qualified Data.HashSet as S

data TopLevel =
    Implementation { funcName         :: Node, arguments    :: [Node], body            :: [Node]                    }
  | Declaration    { declName         :: Node, constraintsD    :: H.HashMap String [Node], declType     :: Node     }
  | Data           { typeName         :: Node, constructors    :: [Node]                    }
  | Instance       { instancing       :: Node, instanced    :: Node, implementations :: H.HashMap String [TopLevel] }
  | Class          { className        :: Node, declarations :: H.HashMap String TopLevel                            }
  | Infix

data AtomType = Identifier | TypeK | Operator | Nat | Real' | Char' | String' | EndOfFile
  deriving (Eq, Show)

type Identificator = (String, Int)

data TypeError = TypeError -- ...

data MonoType =
    Variable    { varIdentifier :: Identificator , vConstraints :: S.HashSet String                  }
  | Constructor { constructor   :: Node , typeArgs     :: [MonoType]                          }
  | Function    { fromClass     :: Bool          , takesType    :: MonoType   , retsType :: MonoType }
  | BuiltinNat | BuiltinReal | BuiltinChar | BuiltinString
  | Bottom -- just for convencience
  deriving (Eq)

data Node =
    Atom           { name       :: String, atomType    :: AtomType , info :: MonoType , pos :: SourcePos        }
  | Lambda         { args       :: [Node], lamExpr     :: Node                                        }
  | Expression     { expression :: [Node]                                                              }
  | BinaryExpr     { leftExpr   :: Node , oper        :: Node  , rightExpr   :: Node               }
  | ConcType       { concName   :: Node , consArgs    :: [Node]                                       }
  | TypeAssertion  { node       :: Node , constraints :: H.HashMap String [Node], choritype :: Node }
  | LocalBind      { locName    :: Node , localBind   :: Node                                         }
    deriving (Eq)

instance Show Node where
  show (Atom n _ _ _)       = n
  show (Lambda a b)         = show "\\" ++ show a ++ " -> " ++ show b
  show (Expression [])      = undefined
  show (Expression (e:es))  = '(' : foldl (\s n -> s ++ ' ' : show n) (show e) es ++ ")"
  show (BinaryExpr le o re) = '(' : show o ++ " " ++ show le ++ " " ++ show re ++ ")"
  show (ConcType n a)       = show n ++ foldl (\s a' -> s ++ ' ' : show a') "" a
  show (TypeAssertion n c t)  = show n ++ " :: " ++ show c ++ " => "++ show t
  show (LocalBind v b)        = "let " ++ show v ++ " = " ++ show b

instance Show TopLevel where
  show (Implementation f a b) = show f ++ ' ' : show a ++ " = " ++ show b
  show (Declaration f c t)    = show f ++ " :: " ++ show c ++ " => " ++ show t
  show (Data n c)           = show n ++ " with constructors " ++ show c
  show (Instance i c m)       = show i ++ " for " ++ show c ++ " where " ++ show m
  show (Class c d)            = show c ++ " where " ++ show d
  show Infix                  = ""

type Precedence = Int
type ParserState = (SourcePos, H.HashMap String Precedence)

atomWithName :: AtomType -> SourcePos -> String -> Node
atomWithName t s n = Atom n t Bottom s

scanChar :: (Monad m) => ParsecT String ParserState m Char -> ParsecT String ParserState m Char
scanChar p = do
  c <- p
  modifyState $ first (if c == '\n' then (`incSourceLine` 1) . (`setSourceColumn` 0) else (`incSourceColumn` 1))
  return c

parseEscapingChars :: (Monad m) => ParsecT String ParserState m Char
parseEscapingChars = scanChar (char '\\' >> escaping) <|> scanChar anyChar
  where escaping = oneOf "'\"\\nrtbfv" :: (Monad m) => ParsecT String ParserState m Char

parseChar :: (Monad m) => ParsecT String ParserState m Node
parseChar = do
  pos' <- fst <$> getState
  atomWithName Char' pos' . (: []) <$> between (char '\'') (char '\'') parseEscapingChars

parseString :: (Monad m) => ParsecT String ParserState m Node
parseString = do
  pos' <- fst <$> getState
  atomWithName String' pos' <$> between (char '\"') (char '\"') (many parseEscapingChars)

parseNum :: (Monad m) => ParsecT String ParserState m Node
parseNum = do
  pos' <- fst <$> getState
  int <- many1 $ scanChar digit
  dec <- option "" $ (:) <$> char '.' <*>  many1 digit
  return $ atomWithName (if null dec then Nat else Real') pos' $ int ++ dec

parseIdentifier :: (Monad m) => ParsecT String ParserState m Node
parseIdentifier = do
  pos' <- fst <$> getState
  initial <- scanChar lower
  atomWithName Identifier pos' . (initial :) <$> many (scanChar alphaNum)

parseTypeK :: (Monad m) => ParsecT String ParserState m Node
parseTypeK = do
  pos' <- fst <$> getState
  initial <- scanChar upper
  atomWithName TypeK pos' . (initial :) <$> many (scanChar alphaNum)

parseOp :: (Monad m) => ParsecT String ParserState m Node
parseOp = do
  pos' <- fst <$> getState
  atomWithName Operator pos' <$> many1 (scanChar $ oneOf "+-*/")

parseLambda :: (Monad m) => ParsecT String ParserState m Node
parseLambda = do
  _ <- char '\\' <|> char 'λ'
  spaces
  lambArgs <- many1 parseIdentifier
  spaces
  _ <- string "->"
  Lambda lambArgs <$> parseValueExpression

parseAtom :: (Monad m) => ParsecT String ParserState m Node
parseAtom = parseIdentifier <|> parseTypeK <|> between (char '(') (char ')') parseBinaryExpression <|> parseNum <|> parseChar <|> parseString

parseExpression :: (Monad m) => ParsecT String ParserState m Node
parseExpression = Expression <$> many1 (do {
  atom <- parseAtom;
  spaces;
  return atom
})

{- TODO: Infixl vs Infixr -}
parseBinaryExpression :: (Monad m) => ParsecT String ParserState m Node
parseBinaryExpression = do
  expr <- parseExpression
  spaces
  mkRest <- do {
    op <- parseOp;
    spaces;
    expr' <- parseBinaryExpression;
    prec <- snd <$> getState;
    return $ addNode prec op expr'
  }  <|> return return
  mkRest expr
  where
    addNode :: (Monad m) => H.HashMap String Int -> Node -> Node -> Node -> m Node
    addNode prec op  expr' expr= return $ insertNode (H.findWithDefault 5 (name op) prec) prec op expr' expr

    insertNode :: Int -> H.HashMap String Int -> Node -> Node -> Node -> Node
    insertNode _ _ op expr'@(Expression _) expr                         = BinaryExpr expr op expr'
    insertNode opPrec prec op expr'@(BinaryExpr lexpr' op' rexpr') expr = let opPrec' = H.findWithDefault 5 (name op') prec
                                                                            in if opPrec' > opPrec
                                                                                then BinaryExpr expr op expr'
                                                                                else BinaryExpr (insertNode opPrec prec op lexpr' expr) op' rexpr'
    insertNode _ _ _ _ _ = undefined

parseLocalBind :: (Monad m) => ParsecT String ParserState m Node
parseLocalBind = do
  _ <- string "let"
  spaces
  bindedName <- parseIdentifier
  spaces
  _ <- char '='
  spaces
  LocalBind bindedName <$> parseBinaryExpression

parseValueExpression :: (Monad m) => ParsecT String ParserState m Node
parseValueExpression = parseLocalBind <|> parseBinaryExpression <|> parseLambda

parseImplementation :: (Monad m) => ParsecT String ParserState m TopLevel
parseImplementation = do
  fName <- parseIdentifier <|> parseOp
  spaces
  fArgs <- many $ parseIdentifier <* spaces
  _ <- char '='
  spaces
  bodyL <- parseValueExpression `sepBy` char ','
  _ <- char ';'
  return $ Implementation fName fArgs bodyL

parseConc :: (Monad m) => ParsecT String ParserState m Node
parseConc = do
  typeConstructor <- parseTypeK
  constructorArgs <- many $ parseIdentifier <|> between (char '(') (char ')') parseType
  return $ ConcType typeConstructor constructorArgs

parseType :: (Monad m) => ParsecT String ParserState m Node
parseType = parseIdentifier <|> parseConc

parseConstraints :: (Monad m) => ParsecT String ParserState m (H.HashMap String [Node])
parseConstraints = between (char '(') (char ')' >> spaces >> string "=>") $ parseConstraint `chainl1` (char ',' >> return (H.unionWith (++)))
  where
  parseConstraint = do {
    cnstraint <- parseTypeK;
    H.singleton (name cnstraint) . (: []) <$> parseIdentifier;
  }

parseTypeParser :: (Monad m) => ParsecT String ParserState m Node -> ParsecT String ParserState m Node
parseTypeParser p = do
  parsed <- p
  spaces
  _ <- string "::"
  spaces
  cnstraints <- option H.empty parseConstraints
  TypeAssertion parsed cnstraints . Expression <$> ((spaces *> parseType <* spaces) `sepBy` string "->") <* char ';'

parseDeclaration :: (Monad m) => ParsecT String ParserState m TopLevel
parseDeclaration = (\(TypeAssertion e c t) -> Declaration e c t) <$> parseTypeParser (parseIdentifier <|> parseOp)

parseData :: (Monad m) => ParsecT String ParserState m TopLevel
parseData = do
  _ <- string "data"
  spaces
  dataName <- parseIdentifier
  spaces
  _ <- char '='
  spaces
  Data dataName <$> parseConc `sepBy` char '|'

parseInstance :: (Monad m) => ParsecT String ParserState m TopLevel
parseInstance = do
  _ <- string "instance"
  spaces
  instancingClass <- parseIdentifier
  spaces
  instanceType <- parseIdentifier
  spaces
  Instance instancingClass instanceType <$> between (char '{') (char '}')
    ((parseImplementation <&> uncurry H.singleton . ((\(Instance n _ _) -> name n) &&& (: [])))
    `chainl1` (char ';' >> return (H.unionWith (++))))

parseClass :: (Monad m) => ParsecT String ParserState m TopLevel
parseClass = do
  _ <- string "class"
  spaces
  classNaming <- parseIdentifier
  spaces
  Class classNaming <$> between (char '{') (char '}')
    ((parseDeclaration <&> uncurry H.singleton . ((\(Class n _) -> name n) &&& id))
    `chainl1` (char ';' >> return H.union))

parseInfix :: (Monad m) => ParsecT String ParserState m TopLevel
parseInfix = do
  _ <- string "infix"
  spaces
  op <- parseOp
  spaces
  prec <- many1 digit
  spaces
  _ <- char ';'
  updateState $ second $ H.insert (name op) ((read :: String -> Int) prec)
  return Infix

parseFunc :: (Monad m) => ParsecT String ParserState m TopLevel
parseFunc = parseImplementation <|> parseDeclaration

parseChoriLang :: (Monad m) => ParsecT String ParserState m [TopLevel]
parseChoriLang = (parseFunc <|> parseData <|> parseDeclaration <|> parseInstance <|> parseClass <|> parseInfix) `sepBy` spaces

parser :: (Monad m) => String -> m (Either ParseError [TopLevel])
parser = runParserT parseChoriLang (initialPos "CommandLine", H.empty) "CommandLine"
