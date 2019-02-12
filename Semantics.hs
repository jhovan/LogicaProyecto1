module Semantics where

import Syntax
import Data.List
type Estado = []

-- La lista de estados, contiene las variables verdaderas
interp :: Prop -> [Estado] -> Bool 
TTrue -> TTrue
FFalse -> FFalse
Neg q -> not q
V x -> elem x e
Conj p q -> (inter e p) && (iner e q)
Disy p q -> (inter e p) || (inter e q)
Imp p q -> not (inter e p) || (inter e q)
Equiv p q -> (interp e p) == (interp e q)

estados :: Prop -> [Estado]
estados phi = subconj(vars phi)

-- 3. Conceptos semanticos

modelos :: Prop -> [Estado]
modelos phi = [e|e <- estados phi, interp e phi]

tautologia :: Prop ->  Bool
tautologia phi = (modelos phi) == (estados phi)

satisfen = interp

satisf :: Prop -> Bool
satisf phi = modelos phi /= []

insatisfen :: Estado -> Prop -> Bool
insatisfen e phi = not(interp e phi)

contrad :: Prop -> Bool
contrad phi = modelos phi == []

pega :: [Prop] -> Prop
pega [] = TTrue
pega [x] = x
pega (x:xs) = Conj x pega(xs)

estadosConj :: [Prop] -> [Estado]
estadosConj l = estados (pega l)

modelosConj :: [Prop] -> [Estado]
modelosConj l = modelos (pega l)

satisfenConj:: Estado -> [Prop] -> Bool
satisfenConj l = satisfen (pega l)

satisfConj:: [Prop] -> Bool
satisfConj l = satisf (pega l)

insatisfenConj:: Estado -> [Prop] -> Bool
insatisfenConj l = insatisfen(pega l)

insatisfConj :: [Prop] -> Bool
insatisfConj l = contrad (pega l)


--Seguirle igual con las otras funciones

-- 4.

equiv :: Prop -> Prop -> Bool
equiv phi psi = tautologia (Equiv phi psi)



-- 5. Consecuencia Logica

consecuencia :: [Prop] -> Prop -> Bool
consecuencia gamma phi = insatisfConj ((No))

-- Terminamos nota 2
-- Agregar semantics y syntax al repositorio

-- Auxiliares

vars :: Prop -> [VarP]
vars phi = case phi of
    TTrue -> []
    V x -> [x]
    Conj p q -> union (vars p) (vars q)
    
subconj :: [a] -> [[a]]
subconj [] = [[]]
subconj (x:xs) = xs' ++ map (x:) xs'
    where xs' = subconj xs 

