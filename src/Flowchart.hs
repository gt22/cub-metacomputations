{-# LANGUAGE TypeFamilies, StandaloneDeriving, FlexibleContexts, Rank2Types, QuantifiedConstraints #-}
module Flowchart where

import qualified Data.List.NonEmpty as NE
import Data.List.NonEmpty (NonEmpty((:|)))
import qualified Data.Map.Strict as M
import Control.Monad.State

newtype Var s = FlowVar Integer deriving (Eq, Ord)

instance Show (Var s) where

    show (FlowVar x) = "x" ++ show x

newtype Label s = FlowLabel String deriving (Eq, Ord)

instance Show (Label s) where

    show (FlowLabel s) = s ++ ":"

data FlowChart t s = Program [Var s] (NE.NonEmpty (FlowBlock t s))


data FlowBlock t s = BasicBlock (Label s) [Assignment t s] (Jump t s)

data Assignment t s = Assn (Var s) (Expr t s)

data Expr t s = Const (Value t) | Lookup (Var s) | Op (Op t s)

data Jump t s = Goto (Label s) | If (Expr t s) (Label s) (Label s) | Return (Expr t s)

deriving instance (ValueClass t) => Show (FlowChart t s)
deriving instance (ValueClass t) => Show (FlowBlock t s)
deriving instance (ValueClass t) => Show (Assignment t s)
deriving instance (ValueClass t) => Show (Expr t s)
deriving instance (ValueClass t) => Show (Jump t s)

deriving instance (ValueClass t) => Eq (FlowChart t s)
deriving instance (ValueClass t) => Eq (FlowBlock t s)
deriving instance (ValueClass t) => Eq (Assignment t s)
deriving instance (ValueClass t) => Eq (Expr t s)
deriving instance (ValueClass t) => Eq (Jump t s)

type ProgramState t s = M.Map (Var s) (Value t)

class (Show (Value t), forall s. Show (Op t s), Eq (Value t), forall s. Eq (Op t s)) => ValueClass t where

    data (Value t)
    data (Op t s)

    reduce_ :: ProgramState t s -> Op t s -> Expr t s

    truthiness :: Value t -> Bool

reduce :: (ValueClass t) => ProgramState t s -> Expr t s -> Expr t s
reduce _ e@(Const _) = e 
reduce s (Op e) = reduce_ s e
reduce s (Lookup v) = case M.lookup v s of
    Nothing -> Lookup v
    (Just v') -> Const v'

binaryReduce :: (ValueClass t) => (Value t -> Value t -> Value t) -> (Expr t s -> Expr t s -> Op t s) -> ProgramState t s -> Expr t s -> Expr t s -> Expr t s
binaryReduce op con s a b = case reduce s a of
        (Const a') -> case reduce s b of
            (Const b') -> Const (op a' b')
            b' -> Op $ con (Const a') b'
        a' -> case reduce s b of
            (Const b') -> Op $ con a' (Const b')
            b' -> Op $ con a' b'

unaryReduce :: (ValueClass t) => (Value t -> Value t) -> (Expr t s -> Op t s) -> ProgramState t s -> Expr t s -> Expr t s
unaryReduce op con s a = case reduce s a of
    (Const a') -> Const $ op a'
    a' -> Op $ con a'


data SimpleInts

instance ValueClass SimpleInts where

    newtype instance (Value SimpleInts) = SimpleInt { unpack :: Integer } deriving (Show, Eq)
    data instance (Op SimpleInts s) = Sum (Expr SimpleInts s) (Expr SimpleInts s)
                                    | Prod (Expr SimpleInts s) (Expr SimpleInts s)
                                    | Neg (Expr SimpleInts s)
                                    deriving (Show, Eq)

    reduce_ s (Sum a b) = binaryReduce (\x y -> SimpleInt $ unpack x + unpack y) Sum s a b
    reduce_ s (Prod a b) = binaryReduce (\x y -> SimpleInt $ unpack x * unpack y) Prod s a b
    reduce_ s (Neg a) = unaryReduce (\x -> SimpleInt $ -unpack x) Neg s a


    truthiness = (/= 0) . unpack

toBlocks :: NonEmpty (FlowBlock t s) -> M.Map (Label s) (FlowBlock t s)
toBlocks bs = M.fromList [(label, blk) | blk@(BasicBlock label _ _) <- NE.toList bs]

eval :: (ValueClass t) => FlowChart t s -> [Value t] -> Value t
eval (Program vars bs@(b :| _)) args = let 
    s = M.fromList (zip vars args)
    in evalState (evalBlock (toBlocks bs) b) s

evalBlock :: (ValueClass t) => M.Map (Label s) (FlowBlock t s) -> FlowBlock t s -> State (ProgramState t s) (Value t)
evalBlock b (BasicBlock _ asn jmp) = do
    mapM_ evalAssign asn
    case jmp of
        (Goto l) -> jump b l
        (If expr t f) -> do
            x <- evalExpr expr
            jump b (if (truthiness x) then t else f)
        (Return expr) -> evalExpr expr

evalAssign :: (ValueClass t) => Assignment t s -> State (ProgramState t s) ()
evalAssign (Assn var expr) = do
    x <- evalExpr expr
    modify $ M.insert var x

evalExpr :: (ValueClass t) => Expr t s -> State (ProgramState t s) (Value t)
evalExpr expr = do
    s <- get
    case reduce s expr of
        (Const x) -> pure x
        _ -> error "Invalid variable references"

jump :: (ValueClass t) => M.Map (Label s) (FlowBlock t s) -> Label s -> State (ProgramState t s) (Value t)
jump b label = case M.lookup label b of
    Nothing -> error "Invalid label"
    (Just blk) -> evalBlock b blk




data GeneratorState = GenState { curVar :: Integer, curLab :: Integer }

emptyGen :: GeneratorState
emptyGen = GenState 0 0

flowchart :: State GeneratorState (FlowChart t s) -> FlowChart t s
flowchart g = evalState g emptyGen

freshVar :: State GeneratorState (Var s)
freshVar = do
    v <- gets curVar
    modify $ \s -> s { curVar = succ v }
    return $ FlowVar v

freshLab' :: State GeneratorState (Label s)
freshLab' = do
    l <- gets $ curLab
    modify $ \s -> s { curLab = succ l }
    return $ FlowLabel $ "lab" ++ show l

freshLab :: State (ChartState t s) (Label s)
freshLab = do
    s <- gets chartGenerator
    let (l, s') = runState freshLab' s
    modify $ \ss -> ss { chartGenerator = s' }
    return l

readVar :: (Var s -> State GeneratorState (FlowChart t s)) -> State GeneratorState (FlowChart t s)
readVar f = do
    v <- freshVar
    (Program vars b) <- f v
    return $ Program (v : vars) b

read2 :: (Var s -> Var s -> State GeneratorState (FlowChart t s)) -> State GeneratorState (FlowChart t s)
read2 f = readVar $ \a -> readVar $ \b -> f a b

read3 :: (Var s -> Var s -> Var s -> State GeneratorState (FlowChart t s)) -> State GeneratorState (FlowChart t s)
read3 f = readVar $ \a -> readVar $ \b -> readVar $ \c -> f a b c

fresh :: (Var s -> State GeneratorState (FlowChart t s)) -> State GeneratorState (FlowChart t s)
fresh f = freshVar >>= f

fresh2 :: (Var s -> Var s -> State GeneratorState (FlowChart t s)) -> State GeneratorState (FlowChart t s)
fresh2 f = fresh $ \a -> fresh $ \b -> f a b

fresh3 :: (Var s -> Var s -> Var s -> State GeneratorState (FlowChart t s)) -> State GeneratorState (FlowChart t s)
fresh3 f = fresh $ \a -> fresh $ \b -> fresh $ \c -> f a b c

data ChartState t s = ChartState { chartGenerator :: GeneratorState, chartBlocks :: [FlowBlock t s] }

blocks :: State (ChartState t s) (Label s) -> State GeneratorState (FlowChart t s)
blocks blk = do
    s <- get
    let (start, s') = runState blk (ChartState s [])
    put $ chartGenerator s'
    firstLabel <- freshLab'
    return $ Program [] (BasicBlock firstLabel [] (Goto start) :| chartBlocks s')

data BlockState t s = BlockState { blockGenerator :: GeneratorState, assns :: [Assignment t s] }

block_ :: Label s -> State (BlockState t s) (Jump t s) -> State (ChartState t s) ()
block_ l b = do
    s <- get
    let (jmp, s') = runState b (BlockState (chartGenerator s) [])
    modify $ \ss -> ss { chartGenerator = blockGenerator s', chartBlocks = chartBlocks ss ++ [BasicBlock l (assns s') jmp] }

block :: State (BlockState t s) (Jump t s) -> State (ChartState t s) (Label s)
block b = do
    l <- freshLab
    block_ l b
    return l

assign :: Var s -> Expr t s -> State (BlockState t s) ()
assign v e = modify $ \s -> s { assns = assns s ++ [Assn v e] }

goto :: Label s -> State (BlockState t s) (Jump t s)
goto = return . Goto

goto_if :: Expr t s -> Label s -> Label s -> State (BlockState t s) (Jump t s)
goto_if e t f = return $ If e t f

returnFc :: Expr t s -> State (BlockState t s) (Jump t s)
returnFc = return . Return