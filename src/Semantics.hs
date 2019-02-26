module Semantics where

import Syntax
import Data.List
type Estado = [VarP]

-- La lista de estados, contiene las variables verdaderas
interp :: Estado -> Prop -> Bool 
interp e phi = case phi of
    TTrue -> True
    FFalse -> False
    Neg q -> not (interp e q)
    V x -> elem x e
    Conj p q -> (interp e p) && (interp e q)
    Disy p q -> (interp e p) || (interp e q)
    Imp p q -> not (interp e p) || (interp e q)
    Equiv p q -> (interp e p) == (interp e q)

-- Obtiene la lista de todos los posibles estados para una proposicion
estados :: Prop -> [Estado]
estados phi = subconj(vars phi)

-- 3. Conceptos semanticos

-- Obtiene todos los modelos de una proposicion
modelos :: Prop -> [Estado]
modelos phi = [e|e <- estados phi, interp e phi]

-- Regresa verdadero si una proposicion es una tautologia
tautologia :: Prop ->  Bool
tautologia phi = (modelos phi) == (estados phi)

-- La funcion satisfacible en, que es basicamente la interpretacion
satisfen = interp

-- Regresa verdadero si la proposicion es satisfacible
satisf :: Prop -> Bool
satisf phi = modelos phi /= []

-- Regresa verdadero si la proposicion es insatisfacible en el estado dado
insatisfen :: Estado -> Prop -> Bool
insatisfen e phi = not(interp e phi)

-- Regresa verdadero si la proposicion es una contradiccion
contrad :: Prop -> Bool
contrad phi = modelos phi == []

-- Junta todas las propociones de un conjunto, en una sola unidas por conjunciones
pega :: [Prop] -> Prop
pega [] = TTrue
pega [x] = x
pega (x:xs) = Conj x (pega xs)

-- Obtiene todos los estados de un conjunto de Proposiciones
estadosConj :: [Prop] -> [Estado]
estadosConj l = estados (pega l)

-- Obtiene todos los modelos de un conjunto de proposiciones
modelosConj :: [Prop] -> [Estado]
modelosConj l = modelos (pega l)

-- Regresa verdadero si el conjunto de proposiciones es satisfacible en un estado dado
satisfenConj:: Estado -> [Prop] -> Bool
satisfenConj e l = satisfen e (pega l)

-- Regresa verdadero si el conjunto es satisfacible
satisfConj:: [Prop] -> Bool
satisfConj l = satisf (pega l)

-- Regresa verdero si el conjunto es insatisfacible en un estado dado
insatisfenConj:: Estado -> [Prop] -> Bool
insatisfenConj e l = insatisfen e (pega l)

-- Regresa verdadero si el conunto es insatisfacible
insatisfConj :: [Prop] -> Bool
insatisfConj l = contrad (pega l)


-- 4.

-- Regresa verdadero si dos proposiciones son equivalentes
equiv :: Prop -> Prop -> Bool
equiv phi psi = tautologia (Equiv phi psi)



-- 5. Consecuencia Logica

-- Regresa verdadero si la consecuencia es un argumento valido
consecuencia :: [Prop] -> Prop -> Bool
consecuencia gamma phi = insatisfConj (Neg phi : gamma)


-- Auxiliares

-- obtiene todas las variables de una formula de logica proposicional
vars :: Prop -> [VarP]
vars phi = case phi of
    TTrue -> []
    FFalse -> []
    V x -> [x]
    Neg q -> vars q
    Conj p q -> union (vars p) (vars q)
    Disy p q -> union (vars p) (vars q)
    Imp p q -> union (vars p) (vars q)
    Equiv p q -> union (vars p) (vars q)
    
-- Obtiene el conjunto potencia de un conjunto
subconj :: [a] -> [[a]]
subconj [] = [[]]
subconj (x:xs) = xs' ++ map (x:) xs'
    where xs' = subconj xs 



