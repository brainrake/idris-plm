||| Simply Typed Lambda Calclulus? not yet
module STLC

import Data.Fin
import Data.Vect


%language DSLNotation

data Ty
    = TyInt
    | TyBool
    | TyFun Ty Ty


interpTy : Ty -> Type
interpTy TyInt = Integer
interpTy TyBool = Bool
interpTy (TyFun a b) = interpTy a -> interpTy b


using (G : Vect n Ty)

    data Expr : Vect n Ty -> Ty -> Type


    data HasType : (i : Fin n) -> Vect n Ty -> Ty -> Type where
        Stop : HasType FZ (t :: G) t
        Pop : HasType k G t -> HasType (FS k) (u :: G) t


    data Expr : Vect n Ty -> Ty -> Type where
        Var : HasType i G t -> Expr G t
        Val : (x : Integer) -> Expr G TyInt
        Lam : Expr (a :: G) t -> Expr G (TyFun a t)
        App : Expr G (TyFun a t) -> Expr G a -> Expr G t
        Op : (interpTy a -> interpTy b -> interpTy c) -> Expr G a -> Expr G b -> Expr G c
        If : Expr G TyBool -> Lazy (Expr G a) -> Lazy (Expr G a) -> Expr G a

    data Env : Vect n Ty -> Type where
        Nil : Env Nil
        (::) : interpTy a -> Env G -> Env (a :: G)


    lookup : HasType i G t -> Env G -> interpTy t
    lookup Stop (x :: xs) = x
    lookup (Pop k) (x :: xs) = lookup k xs


    interp : Env G -> Expr G t -> interpTy t
    interp env (Var i) = lookup i env
    interp env (Val x) = x
    interp env (Lam sc) = \x => interp (x :: env) sc
    interp env (App f s) = interp env f (interp env s)
    interp env (Op op x y) = op (interp env x) (interp env y)
    interp env (If x t e) = if interp env x then interp env t else interp env e


    add : Expr G (TyFun TyInt (TyFun TyInt TyInt))
    add = Lam (Lam (Op (+) (Var Stop) (Var (Pop Stop))))


    fact : Expr G (TyFun TyInt TyInt)
    fact =
        Lam (If
            (Op (==) (Var Stop) (Val 0))
            (Val 1)
            (Op (*)
                (App fact (Op (-) (Var Stop) (Val 1)))
                (Var Stop)))


    mkLam : TTName -> Expr (t::g) t' -> Expr g (TyFun t t')
    mkLam _ body = Lam body


    dsl expr
        variable = Var
        index_first = Stop
        index_next = Pop
        lambda = mkLam


    -- for idiom brackets

    (<*>) : (f : Lazy (Expr G (TyFun a t))) -> Expr G a -> Expr G t
    (<*>) f x = App f x

    pure : Expr G a -> Expr G a
    pure x = x


    -- overload ops


    -- (*) : Expr G TyInt -> Expr G TyInt -> Expr G TyInt
    -- (*) x y = Op (*) x y


    (==) : Expr G TyInt -> Expr G TyInt -> Expr G TyBool
    (==) x y = Op (==) x y


    -- (-) : Expr G TyInt -> Expr G TyInt -> Expr G TyInt
    -- (-) x y = Op (-) x y


    -- implicit
    -- autoApp : (f : TyFun a b) -> ((interpTy a -> interpTy b) -> Expr G a -> Expr G b)
    -- autoApp f = App f


    syntax "if" [c] "then" [t] "else" [e] = If c then t else e


    Num (Expr G TyInt) where
        fromInteger x = Val x
        (*) = Op (*)
        (+) = Op (+)

    Neg (Expr G TyInt) where
        negate x = Op (-) (Val 0) x
        (-) = Op (-)


    -- fact' : Expr G (TyFun TyInt TyInt) -> Expr G (TyFun TyInt TyInt)
    -- fact' = Ap (expr (\x =>
    --     if x == 0 then 1 else x * fact' (x - 1)
    -- ))

    fact' : Expr G (TyFun TyInt TyInt)
    fact' = expr (\x =>
        if x == 0 then 1 else x * [| fact' (x - 1) |]
    )


    main : IO ()
    main = do
        putStr "n: "
        x <- getLine
        printLn (interp [] fact' (cast x))
