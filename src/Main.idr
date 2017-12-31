module Main

import PLM.Syntax.Abstract
import PLM.Syntax.Concrete
import PLM.Axioms


main : IO ()
main = do
    putStrLn (toPlm example1)
    putStrLn (toPlm beingAbstract)
    putStrLn (toPlmBasic beingAbstract)
    --print (subformula (The_SuchThat "x" ([IndVar "x"] `Exemplifies` beingOrdinary) beingAbstract)
