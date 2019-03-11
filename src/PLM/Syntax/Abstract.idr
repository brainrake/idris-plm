||| Principa Logico-Metaphysica
||| Part II, Chapter 7: The Language
module PLM.Syntax.Abstract

import Data.Vect

%access public export


Name : Type
Name = String


||| The possible types of Formulas
||| Propositional Formulas cannot have `Encodes` subformulas
data FormulaType
    = FPropositional
    | FEncoding



mutual

    ||| Individual Terms
    data IndTerm : Type where

        ||| "a₁, a₂, ..." or "a, b, c, d, e", Individual Constants (Names)
        IndConst : Name -> IndTerm

        ||| "x₁, x₂, ..." or "x, y, z, u, v, w" Individual Variables
        IndVar : Name -> IndTerm

        ||| "ιν" or "the individual ν such that ..."
        The_SuchThat : Name -> Formula t -> IndTerm


    ||| Relational Terms
    data RelTerm : Nat -> Type where

        |||| "P₁ⁿ, P₂ⁿ,..." or "Pⁿ, Qⁿ, R,ⁿ, Sⁿ, Tⁿ", n-place Relation Constants (Names)
        RelConst : Name ->  RelTerm n

        ||| "F₁ⁿ, F₂ⁿ, ..." or "Fⁿ, Gⁿ, Hⁿ, Iⁿ, Jⁿ", n-place Relation Variables
        RelVar : Name -> RelTerm n

        ||| "E!" or "being concrete" or "concreteness"
        BeingConcrete : RelTerm (S Z)

        ||| "λν₁...νₙ" or "being individuals ν₁...νₙ such that ..."
        RelLambda : (Vect n Name) -> Formula FPropositional -> RelTerm n

        ||| a propositional formula is a relational term
        RelProp : Formula FPropositional -> RelTerm 0


    ||| Formulas
    data Formula : FormulaType -> Type where

        ||| "¬" or "it is not the case that ..." or "it is false that ..."
        Not : (Formula t -> Formula t)

        ||| "𝒜" or "actually" or "it is actually the case that ..."
        Actually : Formula t -> Formula t

        ||| "◻" or "necessarily" or "it is necessary that ..."
        Necessarily : Formula t -> Formula t

        ||| "→" or "if ..., then ..."
        Implies : Formula t -> Formula t -> Formula t

        ||| "∀α" or "every α such that ..."
        ForAll : Name -> Formula t -> Formula t

        ||| "Πⁿk₁...kₙ" or ""Πklm" or "k₁...kₙ exemplify Πⁿ"
        Exemplifies : Vect n IndTerm -> RelTerm n -> Formula t

        ||| "k₁Π¹" or "kΠ" or "k₁ encodes Π¹"
        Encodes : IndTerm -> RelTerm 1 -> Formula FEncoding

        ||| "Π⁰ is true"
        IsTrue : RelTerm 0 -> Formula t


Combine : FormulaType -> FormulaType -> FormulaType
Combine FPropositional FPropositional = FPropositional
Combine _ _ = FEncoding

FormulaTypeOf : {t : FormulaType } -> (f : Formula t) -> FormulaType
FormulaTypeOf {t} _ = t


Eq FormulaType where
    FPropositional == FPropositional = True
    FEncoding == FEncoding = True
    _ == _ = False


mutual
    eqIndTerm : IndTerm -> IndTerm -> Bool
    eqIndTerm (IndConst n1) (IndConst n2) = n1 == n2
    eqIndTerm (IndVar n1) (IndVar n2) = n1 == n2
    eqIndTerm (The_SuchThat n1 f1) (The_SuchThat n2 f2) = n1 == n2 && eqFormula f1 f2
    eqIndTerm _ _ = False

    eqRelTerm : RelTerm n -> RelTerm m -> Bool
    eqRelTerm (RelConst n1) (RelConst n2) = n1 == n2
    eqRelTerm (RelVar n1) (RelVar n2) = n1 == n2
    eqRelTerm (BeingConcrete) (BeingConcrete) = True
    eqRelTerm (RelLambda ns1 f1) (RelLambda ns2 f2) = toList ns1 == toList ns2 && eqFormula f1 f2
    eqRelTerm (RelProp f1) (RelProp f2) = eqFormula f1 f2
    eqRelTerm _ _ = False

    eqFormula : Formula t1 -> Formula t2 ->  Bool
    eqFormula (Not f1) (Not f2) = eqFormula f1 f2
    eqFormula (Actually f1) (Actually f2) = eqFormula f1 f2
    eqFormula (Necessarily f1) (Necessarily f2) = eqFormula f1 f2
    eqFormula (Implies f1 g1) (Implies f2 g2) = eqFormula f1 f2 && eqFormula g1 g2
    eqFormula (ForAll n1 f1) (ForAll n2 f2) = n1 == n2 && eqFormula f1 f2
    eqFormula (Exemplifies is1 r1) (Exemplifies is2 r2) = eqRelTerm r1 r2 && toList is1 == toList is2
    eqFormula (Encodes i1 r1) (Encodes i2 r2) = eqIndTerm i1 i2 && eqRelTerm r1 r2
    eqFormula (IsTrue r1) (IsTrue r2) = eqRelTerm r1 r2
    eqFormula _ _ = False

    Eq IndTerm where
        (==) = assert_total eqIndTerm

    Eq (RelTerm n) where
        (==) = assert_total eqRelTerm

    Eq (Formula t) where
        (==) = assert_total eqFormula


||| ∧
and : Formula t -> Formula t -> Formula t
and x y =
    Not (x `Implies` Not y)


andR : RelTerm 2
andR =
    RelLambda ["x", "y"] ((IsTrue (RelVar "x")) `and` (IsTrue (RelVar "y")))


||| ∨
or : Formula t -> Formula t -> Formula t
or x y =
    Not x `Implies` y


orR : RelTerm 2
orR =
    RelLambda ["x", "y"] ((IsTrue (RelVar "x")) `or` (IsTrue (RelVar "y")))



||| ≡
equivalent : Formula t -> Formula t -> Formula t
equivalent x y =
    (x `Implies` y) `and` (y `Implies` x)



isEquivalence : Formula t -> Maybe (Formula t, Formula t)
isEquivalence (Not ((a `Implies` b) `Implies` (Not (c `Implies` d)))) =
    if a == d && b == c then
        Just (a, b)
    else
        Nothing
isEquivalence _ = Nothing


||| ∃
exists : Name -> Formula t -> Formula t
exists arg x =
    Not (ForAll arg (Not x))


||| ◇
possibly : Formula t -> Formula t
possibly x =
    Not (Necessarily (Not x))


subformula : Formula t1 -> Formula t2 -> Bool
subformula formula1 formula2 =
    eqFormula formula1 formula2 ||
        case formula2 of
            (Not f) => eqFormula formula1 f
            (ForAll arg f) => eqFormula formula1 f
            (Necessarily f) => eqFormula formula1 f
            (f `Implies` g) => eqFormula formula1 f ||eqFormula formula1 g
            (IsTrue (RelLambda [] f)) => eqFormula formula1 f
            _ => False


example1 : Formula FPropositional
example1 = (Not ([IndConst "a"] `Exemplifies` (RelVar "P"))) `Implies` ([IndConst "b"] `Exemplifies` (RelVar "Q"))


-- O!
beingOrdinary : RelTerm 1
beingOrdinary =
    RelLambda ["_o"]
        ([IndVar "_o"] `Exemplifies` BeingConcrete)


-- A!
beingAbstract : RelTerm 1
beingAbstract =
    RelLambda ["_a"]
        (Not (possibly
            ([IndVar "_a"] `Exemplifies` beingOrdinary)))


-- "=E" idenitity relation for ordinary individuals
identityE : RelTerm 2
identityE =
    RelLambda ["x", "y"]
        (and
            (Necessarily
                (ForAll "F"
                    (equivalent
                        ([IndVar "x"] `Exemplifies` (RelVar "F"))
                        ([IndVar "y"] `Exemplifies` (RelVar "F")))))
            (and
                ([IndVar "x"] `Exemplifies` beingOrdinary)
                ([IndVar "y"] `Exemplifies` beingOrdinary)))


-- identity for individuals (ordinary or abstract)
identicalInd : IndTerm -> IndTerm -> Formula FEncoding
identicalInd i1 i2 =
    or
        ([i1, i2] `Exemplifies` identityE)
        (and
            (and
                ([i1] `Exemplifies` beingAbstract)
                ([i2] `Exemplifies` beingAbstract))
            (Necessarily
                (ForAll "F"
                    (equivalent
                        (i1 `Encodes` (RelVar "F"))
                        (i2 `Encodes` (RelVar "F"))))))


identicalRel1 : RelTerm 1 -> RelTerm 1 -> Formula FEncoding
identicalRel1 r1 r2 =
    (Necessarily
        (ForAll "x"
            (equivalent
                ((IndVar "x") `Encodes` r1)
                ((IndVar "x") `Encodes` r2))))


identicalRel0 : RelTerm 0 -> RelTerm 0 -> Formula FEncoding
identicalRel0 r1 r2 =
    identicalRel1 (RelLambda ["y"] (IsTrue r1)) (RelLambda ["y"] (IsTrue r2))


identicalRelN : { n : Nat } -> RelTerm n -> RelTerm n -> Formula FEncoding
identicalRelN {n} r1 r2 =
    ?identicalRelN


identicalRel : { n : Nat } -> RelTerm n -> RelTerm n -> Formula FEncoding
identicalRel {n = Z}  = identicalRel0
identicalRel {n = S Z}  = identicalRel1
identicalRel {n} = identicalRelN


notIdenticalInd : IndTerm -> IndTerm -> Formula FEncoding
notIdenticalInd i1 i2 = Not (identicalInd i1 i2)


notIdenticalRel : RelTerm n -> RelTerm n -> Formula FEncoding
notIdenticalRel r1 r2 = Not (identicalRel r1 r2)


substitute : String -> String -> Formula t -> Formula t
substitute x y f =
    f


-- mkLam : TTName -> Expr (t::g) g' -> Expr g (TyFun t t')
-- mkLam _ body = Lam a


-- dsl plm
--     variable = IndVar
--     index_first = Stop
--     index_next = Pop
--     lambda = mkLam




data Ty
    = TyInd
    | TyRel Nat
    | TyFun Ty Ty


tyFormula : {t : FormulaType} -> Formula t -> Ty
tyFormula {t = FPropositional} (Not f) = tyFormula f
tyFormula (Actually f) = tyFormula f
tyFormula (Necessarily f) = tyFormula f
tyFormula (Implies f g) = TyFun (tyFormula f) (tyFormula g)
tyFormula (ForAll n f) = tyFormula f
tyFormula (Exemplifies is r) = TyInd
tyFormula (Encodes i r) = TyInd
tyFormula (IsTrue r) = TyInd
