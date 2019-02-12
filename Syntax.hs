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


elimEquiv :: Prop -> Prop
elimEquiv (Equiv p q) = Conj (Imp p q) (Im q p)
--para cualquier otro caso
elimEquiv p = p

elimImp :: Prop -> Prop
elimImp(Imp p q) = Disy (Neg p) q
--para cualquier otro caso 
elimImp p = p 
