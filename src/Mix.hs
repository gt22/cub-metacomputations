{-# LANGUAGE TypeFamilies, StandaloneDeriving, FlexibleInstances #-}
module Mix where

import Flowchart
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import Data.List.NonEmpty (NonEmpty((:|)))
import Data.List.NonEmpty.Extra ((|>))
import Data.List.Extra (snoc)
import Control.Monad.State
import Debug.Trace


type StaticState t s = M.Map (Var s) (Value t)
data MixState t s = MixState { 
    pending :: [(Label s, StaticState t s)], 
    marked :: S.Set (Label s), 
    residual :: FlowChart t s 
}

data MixBlockState t s = MixBlockState {
    mixState :: MixState t s,
    staticState :: StaticState t s,
    dynamicAssignments :: [Assignment t s]
}

staticLabel :: (ValueClass t) => Label s -> StaticState t s -> Label s
staticLabel (FlowLabel l) = FlowLabel . M.foldlWithKey (\acc x v -> acc ++ "(" ++ show x ++ "=" ++ show v ++ ")") (l ++ "_static_")

mix :: (ValueClass t) => FlowChart t s -> StaticState t s -> FlowChart t s
mix (Program args bs@((BasicBlock ini _ _) :| _)) vs = evalState (mixLoop $ toBlocks bs) $ MixState { 
        pending = [(ini, vs)], 
        marked = S.singleton l, 
        residual = Program [v | v <- args, M.notMember v vs] (BasicBlock ini [] (Goto l) :| [])
    }
    where
        l = staticLabel ini vs

mixLoop :: (ValueClass t) => M.Map (Label s) (FlowBlock t s) -> State (MixState t s) (FlowChart t s)
mixLoop bs = do
    p <- gets pending
    case p of
        [] -> gets residual
        ((l, vs) : ps) -> do
            modify $ \m -> m { pending = ps }
            s <- get
            let (bb, s') = runState (mixGoto (staticLabel l vs) bs l) (MixBlockState { mixState = s, staticState = vs, dynamicAssignments = [] })
            put $ mixState s'
            modify $ \m -> let (Program args bs') = residual m in m { residual = Program args (bs' |> bb) }
            mixLoop bs

mixBlock :: (ValueClass t) => M.Map (Label s) (FlowBlock t s) -> Label s -> FlowBlock t s -> State (MixBlockState t s) (FlowBlock t s)
mixBlock bs l (BasicBlock _ asn jmp) = do
    mapM_ mixAssn asn
    vs <- gets staticState
    as <- gets dynamicAssignments
    case jmp of
        (Goto l') -> mixGoto l bs l'
        (If e t f) -> case reduce vs e of
            (Const v) -> mixGoto l bs $ if truthiness v then t else f
            e' -> do
                pend t
                pend f
                return $ BasicBlock l as (If e' (staticLabel t vs) (staticLabel f vs))
        (Return e) -> return $ BasicBlock l as (Return (reduce vs e))

mixAssn :: (ValueClass t) => Assignment t s -> State (MixBlockState t s) ()
mixAssn (Assn x e) = do
    vs <- gets staticState
    case reduce vs e of
        (Const v) -> modify $ \s -> s { staticState = M.insert x v vs }
        e' -> modify $ \s -> s { dynamicAssignments = dynamicAssignments s `snoc` (Assn x e') }

mixGoto :: (ValueClass t) => Label s -> M.Map (Label s) (FlowBlock t s) -> Label s -> State (MixBlockState t s) (FlowBlock t s)
mixGoto l' bs l = do
    let b = M.lookup l bs
    case b of
        Nothing -> error "Invalid label"
        (Just b') -> mixBlock bs l' b'

pend :: (ValueClass t) => Label s -> State (MixBlockState t s) ()
pend l = do
    m <- gets mixState
    vs <- gets staticState
    let l' = staticLabel l vs
    case S.member l' (marked m) of
        True -> pure ()
        False -> modify $ \s -> s { mixState = m { pending = (l, vs) : pending m, marked = S.insert l' (marked m) } }

-- data FlowchartRepr t' s'
-- type T = FlowchartRepr
-- type E t' s' = Expr (T t' s')

-- deriving instance (ValueClass t') => Show (Value (FlowchartRepr t' s'))
-- deriving instance (ValueClass t') => Eq (Value (FlowchartRepr t' s'))
-- instance (ValueClass t') => ValueClass (FlowchartRepr t' s') where

--     data (Value (FlowchartRepr t' s')) = StaticState (M.Map (Var s') (Value t'))
--                                        | StaticVar (Var s')
--                                        | StaticVal (Value t')
--                                        | StaticPartialBlock (Label s') [Assignment t' s']
--                                        | StaticBlock (Label s') [Assignment t' s'] (Jump t' s')
--                                        | StaticProgram (FlowChart t' s')
--                                        | StaticExpr (Expr t' s')
--                                        | StaticBool Bool
--     data (Op (FlowchartRepr t' s') s) = StaticAssign (E t' s' s) (E t' s' s) (E t' s' s) -- var; expr; state -> state
--                                       | DynamicAssign (E t' s' s) (E t' s' s) (E t' s' s) -- block; var; expr -> block
--                                       | BlockLookup (E t' s' s) (E t' s' s) -- label; program -> block
--                                       | StaticReduce (E t' s' s) (E t' s' s) -- expr; state -> expr
--                                       | IsConst (E t' s' s) -- expr -> bool
--         deriving (Show, Eq)

--     reduce_ _ _ = undefined
--     truthiness _ = undefined 


-- flowchart_mix = flowchart $ read3 $ \program