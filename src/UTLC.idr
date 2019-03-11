module STLC

||| Untyped Lambda Calculus

mutual
    Env : Type
    Env = List (String, Value) 


    data Typ : Type where
        FunctionTyp : Typ -> Typ -> Typ
        NaturalTyp : Nat -> Typ


    data Exp : Type where
        Lambda : String -> Exp -> Exp
        Apply : Exp -> Exp -> Exp
        Var : String -> Exp
        Literal : Value -> Exp
        Plus : Exp -> Exp -> Exp


    data Value : Type where
        Closure : Env -> String -> Exp -> Value
        Natural : Nat -> Value


    eval : Env -> Exp -> Value
    eval env (Lambda argname exp) =
        Closure env argname exp
    eval env (Apply f exp) =
        STLC.apply (eval env f) (eval env exp)
    eval env (Literal x) =
        x
    eval env (Var name) =
        lookup name env
    eval env (Plus x y) =
        case (eval env x, eval env y) of
            (Natural x, Natural y) => Natural (x + y)
            _ => ?type_error_plus_not_nat


    apply : Value -> Value -> Value
    apply (Closure env argname exp) arg  =
        eval ((argname, arg) :: env) exp
    apply _ arg =
        ?type_error_apply_not_function


    lookup : String -> Env -> Value
    lookup name [] =
        ?name_error
    lookup name ((n, v) :: xs) =
        if name == n
        then v
        else lookup name xs


exp : Exp
exp = (Apply (Lambda "x" (Plus (Var "x") (Var "x"))) (Literal (Natural 4)))


val : Value
val = eval [] exp
