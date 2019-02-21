module Syntax where

-- | VarP. Tipo que representa las variables proposicionales
type VarP = Int

-- | Prop. Tipo que representa formulas de logica proposicional
data Prop = TTrue
          | FFalse
          | V VarP
          | Neg Prop
          | Conj Prop Prop
          | Disy Prop Prop
          | Imp Prop Prop
          | Equiv Prop Prop

    
instance Show Prop where
    show phi = case phi of
        TTrue -> "T"
        FFalse -> "F"
        V x -> show x
        Neg p -> "(~" ++ show p ++ ")"
        Conj p q -> "(" ++ show p ++ " ^ " ++ show q ++ ")"
        Disy p q -> "(" ++ show p ++ " v " ++ show q ++ ")"
        Imp p q -> "(" ++ show p ++ " -> " ++ show q ++ ")"
        Equiv p q -> "(" ++ show p ++ " <-> " ++ show q ++ ")"
    


elimEquiv :: Prop -> Prop
elimEquiv phi = case phi of

    Neg p -> Neg (elimEquiv p)
    Conj p q -> Conj (elimEquiv p) (elimEquiv q)
    Disy p q -> Disy (elimEquiv p) (elimEquiv q)
    Imp p q -> Imp (elimEquiv p) (elimEquiv q)
    Equiv p q -> Conj (Imp p' q') (Imp q' p')
        where p' = elimEquiv p
              q' = elimEquiv q
    -- culquier otro caso
    _ -> phi 

elimImp :: Prop -> Prop
elimImp phi = case phi of

    Neg p -> Neg (elimImp p)
    Conj p q -> Conj (elimImp p) (elimImp q)
    Disy p q -> Disy (elimImp p) (elimImp q)
    Imp p q -> Disy (Neg(elimImp p)) (elimImp q)
    Equiv p q -> Equiv (elimImp p) (elimImp q)
    -- culquier otro caso
    _ -> phi 

