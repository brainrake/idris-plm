module Axioms

import PLM.Syntax.Abstract

%access public export



data Axiom : (t : FormulaType) -> Type where
    ImpliesIntro : (Formula t) -> (Formula t) -> Axiom t
    ImpliesTrans : (Formula t) -> (Formula t) -> (Formula t) -> Axiom t
    NotImplies : (Formula t) -> (Formula t) -> Axiom t
    ActuallyNot : (Formula t) -> Axiom t
    ActuallyImplies : (Formula t) -> (Formula t) -> Axiom t
    ActuallyForAll : (Formula t) -> Axiom t
    ActuallyActually : (Formula t) -> Axiom t
    NecessarilyImplies : (Formula t) -> (Formula t) -> Axiom t
    NecessaryTrue : (Formula t) -> Axiom t
    PossiblyNecessarily : (Formula t) -> Axiom t
    ActualNecessary : (Formula t) -> Axiom t
    NecessaryActual : (Formula t) -> Axiom t
    Description : (Formula FEncoding) -> Axiom FEncoding




implies_intro : Formula t -> Formula t -> Formula t
implies_intro f g =
    f `Implies` (g `Implies` f)


implies_trans : Formula t -> Formula t -> Formula t -> Formula t
implies_trans f g h =
    (f `Implies` (g `Implies` h)) `Implies` ((f `Implies` g) `Implies` (g `Implies` h))


not_implies : Formula t -> Formula t -> Formula t
not_implies f g =
    (Not f `Implies` Not g) `Implies` ((Not f `Implies` g) `Implies` f)






actually_not : Formula t -> Formula t
actually_not f =
    (Actually (Not f)) `equivalent` (Not (Actually f))


actually_implies : Formula t -> Formula t -> Formula t
actually_implies f g =
    (Actually (f `Implies` g)) `equivalent` (Actually f `Implies` Actually g)


actually_forall : Formula t -> Formula t
actually_forall f =
    (Actually (ForAll "x" f)) `equivalent` (ForAll "x" (Actually f))


actually_actually : Formula t -> Formula t
actually_actually f =
    (Actually f) `equivalent` (Actually (Actually f))


necessarily_implies : Formula t -> Formula t -> Formula t
necessarily_implies f g =
    (Necessarily (f `Implies` g)) `Implies` (Necessarily f `Implies` Necessarily g)


necessary_true : Formula t -> Formula t
necessary_true f =
    Necessarily f `Implies` f


possibly_necessarily : Formula t -> Formula t
possibly_necessarily f =
    possibly f `Implies` Necessarily (possibly f)


actual_necessary : Formula t -> Formula t
actual_necessary f =
    Actually f `Implies` Necessarily (Actually f)


necessary_actual : Formula t -> Formula t
necessary_actual f =
    Necessarily f `equivalent` Actually (Necessarily f)


description : Formula FEncoding -> Formula FEncoding
description f =
    equivalent
        ((IndVar "x") `identicalInd` (The_SuchThat "x" f))
        (ForAll "z" (Actually (substitute "x" "z" f `equivalent` ((IndVar "z") `identicalInd` (IndVar "x")))))




interp : Axiom t -> Formula t
interp (ImpliesIntro f g) = implies_intro f g
interp (ImpliesTrans f g h) = implies_trans f g h
interp (NotImplies f g) = not_implies f g
interp (ActuallyNot f) = actually_not f
interp (ActuallyImplies f g) = actually_implies f g
interp (ActuallyForAll f) = actually_forall f
interp (ActuallyActually f) = actually_actually f
interp (NecessarilyImplies f g) = necessarily_implies f g
interp (NecessaryTrue f) =necessary_true f
interp (PossiblyNecessarily f) = possibly_necessarily f
interp (ActualNecessary f) = actual_necessary f
interp (NecessaryActual f) = necessary_actual f
interp (Description f) = description f
