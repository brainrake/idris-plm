module PLM.Syntax.Concrete

import Data.Vect
import PLM.Syntax.Abstract

%access public export


interface ToPlm a where
    toPlm : a -> String

interface ToPlmBasic a where
    toPlmBasic : a -> String


mutual
    toPlmIndTermBasic : IndTerm -> String
    toPlmIndTermBasic (IndConst name) = name
    toPlmIndTermBasic (IndVar name) = name
    toPlmIndTermBasic (The_SuchThat name formula) = "ι" ++ name ++ " " ++ toPlmFormulaBasic formula


    toPlmRelTermBasic : RelTerm n -> String
    toPlmRelTermBasic (RelConst name) = name
    toPlmRelTermBasic (RelVar name) = name
    toPlmRelTermBasic (BeingConcrete) = "E!"
    toPlmRelTermBasic (RelLambda names formula) = "(λ" ++ concat names ++ " " ++ toPlmFormulaBasic formula ++ ")"
    toPlmRelTermBasic (RelProp formula) = toPlmFormulaBasic formula


    toPlmFormulaBasic : Formula t ->  String
    toPlmFormulaBasic (Implies formula1 formula2) = toPlmFormulaBasic formula1 ++ "→" ++ toPlmFormulaBasic formula2
    toPlmFormulaBasic (Not formula) = "¬" ++ toPlmFormulaBasic formula
    toPlmFormulaBasic (Actually formula) = "𝒜" ++ toPlmFormulaBasic formula
    toPlmFormulaBasic (Necessarily formula) = "◻" ++ toPlmFormulaBasic formula
    toPlmFormulaBasic (ForAll name formula) = "∀" ++ name ++ " " ++ toPlmFormulaBasic formula
    toPlmFormulaBasic (Exemplifies individuals relation) = toPlmRelTermBasic relation ++ concat (map toPlmIndTermBasic individuals)
    toPlmFormulaBasic (Encodes individual relation) = toPlmIndTermBasic individual ++ toPlmRelTermBasic relation
    toPlmFormulaBasic (IsTrue relation) = toPlmRelTermBasic relation


    toPlmIndTerm : IndTerm -> String
    toPlmIndTerm (IndConst name) = name
    toPlmIndTerm (IndVar name) = name
    toPlmIndTerm (The_SuchThat name formula) = "ι" ++ name ++ " " ++ toPlmFormula formula


    toPlmRelTerm : RelTerm n -> String
    toPlmRelTerm (RelConst name) = name
    toPlmRelTerm (RelVar name) = name
    toPlmRelTerm (BeingConcrete) = "E!"
    toPlmRelTerm (RelLambda ["_o"] _) = "O!"
    toPlmRelTerm (RelLambda ["_a"] _) = "A!"
    toPlmRelTerm (RelLambda names formula) = "(λ" ++ concat names ++ " " ++ toPlmFormula formula ++ ")"
    toPlmRelTerm (RelProp formula) = toPlmFormula formula


    toPlmFormula : Formula t ->  String
    toPlmFormula (Not (x `Implies` (Not y))) =  toPlmFormula x ++ "∧" ++ toPlmFormula y
    toPlmFormula ((Not x) `Implies` y) = toPlmFormula x ++ "∨" ++ toPlmFormula y
    toPlmFormula (Not (Necessarily (Not x))) = "◇" ++ toPlmFormula x
    toPlmFormula (Not (ForAll arg (Not x))) = "∃" ++ arg ++ " " ++ toPlmFormula x
    --
    toPlmFormula (Implies formula1 formula2) with (isEquivalence (Implies formula1 formula2))
        | Just (x, y) = "(" ++ toPlmFormula x ++ "=" ++ toPlmFormula y ++ ")"
        | _ = toPlmFormula formula1 ++ "→" ++ toPlmFormula formula2
    toPlmFormula (Not formula) = "¬" ++ toPlmFormula formula
    toPlmFormula (Actually formula) = "𝒜" ++ toPlmFormula formula
    toPlmFormula (Necessarily formula) = "◻" ++ toPlmFormula formula
    toPlmFormula (ForAll name formula) = "∀" ++ name ++ " " ++ toPlmFormula formula
    toPlmFormula (Exemplifies individuals relation) = toPlmRelTerm relation ++ concat (map toPlmIndTerm individuals)
    toPlmFormula (Encodes individual relation) = toPlmIndTerm individual ++ toPlmRelTerm relation
    toPlmFormula (IsTrue relation) = toPlmRelTerm relation


    ToPlm IndTerm where
        toPlm = assert_total toPlmIndTerm


    ToPlm (RelTerm n) where
        toPlm = assert_total toPlmRelTerm


    ToPlm (Formula t) where
        toPlm = assert_total toPlmFormula


    ToPlmBasic IndTerm where
        toPlmBasic = assert_total toPlmIndTermBasic


    ToPlmBasic (RelTerm n) where
        toPlmBasic = assert_total toPlmRelTermBasic


    ToPlmBasic (Formula t) where
        toPlmBasic = assert_total toPlmFormulaBasic
