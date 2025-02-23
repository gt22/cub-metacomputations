{-# LANGUAGE TypeFamilies #-}
{-# OPTIONS_GHC -Wno-incomplete-uni-patterns #-}
{-# OPTIONS_GHC -Wno-incomplete-patterns #-}
module TuringMachine where

import Flowchart

data TuringMachine

type TapeValue = Integer

data Instruction = TMRight | TMLeft | TMWrite TapeValue | TMGoto Instruction | TMIf TapeValue Instruction deriving (Show, Eq)

instance ValueClass TuringMachine where

    data (Value TuringMachine) = Symbol TapeValue
                               | Tape [TapeValue]
                               | Inst Instruction
                               | Instructions [Instruction]
                               | SyntaxError Instruction
                               deriving (Show, Eq)
    data (Op TuringMachine s) = Cons (Expr TuringMachine s) (Expr TuringMachine s)
                              | FirstSymbol (Expr TuringMachine s)
                              | RestSymbols (Expr TuringMachine s)
                              | NewTail (Expr TuringMachine s) (Expr TuringMachine s)
                              | FirstInstruction (Expr TuringMachine s)
                              | RestInstructions (Expr TuringMachine s)
                              | SymEq (Expr TuringMachine s) (Expr TuringMachine s)
                              | FirstParam (Expr TuringMachine s)
                              | SecondParam (Expr TuringMachine s)
                              | CheckOperator Instruction (Expr TuringMachine s)
                              | MakeError (Expr TuringMachine s)
                              deriving (Show, Eq)

    reduce_ s (Cons a b) = binaryReduce (\(Symbol x) (Tape t) -> Tape (x:t)) Cons s a b
    reduce_ s (FirstSymbol t) = unaryReduce (\(Tape (x:_)) -> Symbol x) FirstSymbol s t
    reduce_ s (RestSymbols t) = unaryReduce (\(Tape (_:xs)) -> Tape xs) RestSymbols s t
    reduce_ s (NewTail a b) = binaryReduce (\(Inst q) (Instructions t) -> Instructions (q:t)) NewTail s a b
    reduce_ s (FirstInstruction t) = unaryReduce (\(Instructions (x:_)) -> Inst x) FirstInstruction s t
    reduce_ s (RestInstructions t) = unaryReduce (\(Instructions (_:xs)) -> Instructions xs) RestInstructions s t
    reduce_ s (SymEq a b) = binaryReduce (\(Symbol x) (Symbol x') -> if x == x' then Symbol 1 else Symbol 0) SymEq s a b
    reduce_ s (FirstParam t) = unaryReduce (\(Inst i) -> case i of
            TMWrite x -> Symbol x
            TMGoto q -> Inst q
            TMIf x _ -> Symbol x
        ) FirstParam s t
    reduce_ s (SecondParam t) = unaryReduce (\(Inst (TMIf _ q)) -> Inst q) SecondParam s t
    reduce_ s (CheckOperator q a) = unaryReduce (\(Inst q') -> case (q, q') of
            (TMRight, TMRight) -> Symbol 1
            (TMLeft, TMLeft) -> Symbol 1
            (TMWrite _, TMWrite _) -> Symbol 1
            (TMGoto _, TMGoto _) -> Symbol 1
            (TMIf _ _, TMIf _ _) -> Symbol 1
            _ -> Symbol 0
        ) (CheckOperator q) s a
    reduce_ s (MakeError q) = unaryReduce (\(Inst q') -> SyntaxError q') MakeError s q
    
    truthiness (Symbol s) = s == 0
    truthiness (Tape t) = t == []
    truthiness (Inst _) = True
    truthiness (Instructions q) = q == []
    truthiness (SyntaxError _) = True

turingMachine :: FlowChart TuringMachine s
turingMachine = flowchart $ read2 $ \q right -> 
    fresh3 $ \qTail left instruction -> fresh2 $ \symbol nextlabel -> blocks $ do
        loop <- freshLab
        doRight <- block $ do
            assign left (Op $ Cons (Op $ FirstSymbol (Lookup right)) (Lookup left))
            assign right (Op $ RestInstructions (Lookup right))
            goto loop
        doLeft <- block $ do
            assign right (Op $ Cons (Op $ FirstSymbol (Lookup left)) (Lookup right))
            assign left (Op $ RestInstructions (Lookup left))
            goto loop
        doWrite <- block $ do
            assign symbol (Op $ FirstParam (Lookup instruction))
            assign right (Op $ Cons (Lookup symbol) (Op $ RestSymbols (Lookup right)))
            goto loop
        doJump <- block $ do
            assign qTail (Op $ NewTail (Lookup nextlabel) (Lookup qTail))
            goto loop
        doGoto <- block $ do
            assign nextlabel (Op $ FirstParam (Lookup instruction))
            goto doJump
        doIf <- block $ do
            assign symbol (Op $ FirstParam (Lookup instruction))
            assign nextlabel (Op $ SecondParam (Lookup instruction))
            goto_if (Op $ SymEq (Lookup symbol) (Op $ FirstSymbol (Lookup right))) doJump loop
        doError <- block $ returnFc (Op $ MakeError (Lookup instruction))
        cont5 <- block $ goto_if (Op $ CheckOperator (TMIf undefined undefined) (Lookup instruction)) doIf doError
        cont4 <- block $ goto_if (Op $ CheckOperator (TMGoto undefined) (Lookup instruction)) doGoto cont5
        cont3 <- block $ goto_if (Op $ CheckOperator (TMWrite undefined) (Lookup instruction)) doWrite cont4
        cont2 <- block $ goto_if (Op $ CheckOperator TMLeft (Lookup instruction)) doLeft cont3
        cont1 <- block $ goto_if (Op $ CheckOperator TMRight (Lookup instruction)) doRight cont2
        cont <- block $ do
            assign instruction (Op $ FirstInstruction (Lookup qTail))
            assign qTail (Op $ RestInstructions (Lookup qTail))
            goto cont1
        stop <- block $ returnFc $ Lookup right
        block_ loop $ goto_if (Lookup qTail) stop cont
        block $ do
            assign qTail (Lookup q)
            assign left (Const $ Tape [])
            goto loop