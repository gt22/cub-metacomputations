module Main (main) where

import Flowchart
import Mix
import TuringMachine
import qualified Data.Map.Strict as M

turingProgram = Instructions [TMIf 0 3, TMRight, TMGoto 0, TMWrite 1]

mixedMachine = mix turingMachine (M.fromList [(FlowVar 0, turingProgram)])

main :: IO ()
main = print $ mixedMachine
