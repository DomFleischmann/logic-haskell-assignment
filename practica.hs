---
--- Pracitca Individual, Programacion Declarativa
---             Dominik Fleischmann
---

type Var = String -- nombres de variables
data FProp = V Var | No FProp | Y FProp FProp | O FProp FProp | Si FProp FProp | Sii FProp FProp 

instance Eq FProp where
    V str1 == V str2        = (str1 == str2)
    No x1 == No x2          = (x1 == x2)
    Y x1 y1 == Y x2 y2      = ((x1 == x2) && (y1 == y2)) || ((x1 == y2) && (y1 == x2))
    O x1 y1 == O x2 y2      = ((x1 == x2) && (y1 == y2)) || ((x1 == y2) && (y1 == x2))
    Si x1 y1 == Si x2 y2    = ((x1 == x2) && (y1 == y2))
    Sii x1 y1 == Sii x2 y2  = ((x1 == x2) && (y1 == y2)) || ((x1 == y2) && (y1 == x2))
    _ == _                  = False

instance Ord FProp where
    f1 <= f2     = consecuencia f1 f2

instance Show FProp where
    show (V a)          = a
    show (No f)         = "~" ++ show(f)
    show (Y f1 f2)      = "(" ++ show(f1) ++ " ^ " ++ show(f2) ++ ")"
    show (O f1 f2)      = "(" ++ show(f1) ++ " v " ++ show(f2) ++ ")"
    show (Si f1 f2)     = "(" ++ show(f1) ++ " -> " ++ show(f2) ++ ")"
    show (Sii f1 f2)    = "(" ++ show(f1) ++ " <-> " ++ show(f2) ++ ")"

-- VARS
vars::FProp -> [Var]
vars (V a)          = [a]
vars (No f)         = checkList (vars f)
vars (Y f1 f2)      = checkList (vars f1 ++ vars f2)
vars (O f1 f2)      = checkList (vars f1 ++ vars f2)
vars (Si f1 f2)     = checkList (vars f1 ++ vars f2)
vars (Sii f1 f2)    = checkList (vars f1 ++ vars f2)

-- Quita repeticiones en una lista
checkList::Eq a => [a] -> [a]
checkList []        = []
checkList (l:ls)         =  checkList'  l ( l `elem` (checkList ls)) (checkList  ls)

checkList':: Eq a => a->Bool->[a]->[a]
checkList' e False l    = e:l 
checkList' e True l     = l 


-- TAUTOLOGIA
tautologia::FProp -> Bool
tautologia (V a)    = False
tautologia f1       = foldl (&&) True (tabladeverdad f1) 

-- SATISFACTIBLE
satisfactible::FProp -> Bool
satisfactible (V a)     = True
satisfactible f1        = foldl (||) False (tabladeverdad f1)

-- CONSECUENCIA
consecuencia::FProp -> FProp -> Bool
consecuencia f1 f2 = foldl (&&) True (zipWith (siaux) (tabladeverdad f1) (tabladeverdad f2))

-- EQUIVALENTE
equivalente::FProp -> FProp -> Bool
equivalente f1 f2 = foldl (&&) True (zipWith (==) (tabladeverdad f1) (tabladeverdad f2))

-- CONSECUENCIAS
consecuencias::[FProp] -> [(FProp,[FProp])]
consecuencias fs = consecuencias' fs fs 

consecuencias'::[FProp]->[FProp]->[(FProp,[FProp])]
consecuencias' [] _         = []
consecuencias' (f:fs1) fs2  = (f,(filter (consecuencia f) fs2)) : (consecuencias' fs1 fs2)

-- EQUIVALENTES
equivalentes::[FProp] -> [[FProp]]
equivalentes fs = checkList(map (\x-> filter (equivalente x) fs) fs)


---
--- FUNCIONES AUXILIARES
---

---
--- Funcion que genera la tabla de verdad de una formula
---
tabladeverdad::FProp->[Bool]
tabladeverdad (V a)         = [True, False]
tabladeverdad (No f)        = map (not) (tabladeverdad f)
tabladeverdad f1            = map (evaluaiter f1 (vars f1)) (varsyvalores f1) 

---
--- Evalua una combinacion de valores que pueden tener las variables; por ejemplo, a= True, b= False, a ^ b = False
---
evaluaiter::FProp->[Var]->[Bool]->Bool
evaluaiter (V a) l1 l2          = l2!!(posicionenlista l1 a)
evaluaiter (No f) l1 l2         = not (evaluaiter f l1 l2)
evaluaiter (Y f1 f2) l1 l2      = (evaluaiter f1 l1 l2) && (evaluaiter f2 l1 l2)
evaluaiter (O f1 f2) l1 l2      = (evaluaiter f1 l1 l2) || (evaluaiter f2 l1 l2)
evaluaiter (Si f1 f2) l1 l2     = siaux (evaluaiter f1 l1 l2) (evaluaiter f2 l1 l2)
evaluaiter (Sii f1 f2) l1 l2    = siiaux (evaluaiter f1 l1 l2) (evaluaiter f2 l1 l2)

---
--- Genera una lista de las possibles combinaciones de valores que pueden tener las variables; 
--- por ejemplo para a y b [[True,True],[True,False],[False,True],[False,False]]
---
varsyvalores::FProp->[[Bool]]
varsyvalores (V a)  = [[True], [False]]
varsyvalores f1     = generaiteraciones (listadevalores (2^(length (vars f1))) (length (vars f1))) (2^(length (vars f1)))

---
--- Intercala los valores posibles de cada variable para generar iteraciones de todas las combinaciones posibles;
--- por ejemplo pasa [[True,True,False,False], [True,False,True,False]] a [[True,True],[True,False],[False,True],[False,False]]
--- 
generaiteraciones::[[Bool]]->Int->[[Bool]]
generaiteraciones ls 0  = []
generaiteraciones ls x  = (map (head) ls) : (generaiteraciones (map (tail) ls) (x-1)) 

---
--- Genera una lista de valores que puede tomar cada variable;
--- por ejemplo para a y b [[True,True,False,False], [True,False,True,False]]
---
listadevalores::Int->Int->[[Bool]]
listadevalores n 1 = (crearlista n 1 1 True) : []
listadevalores n x = (crearlista n (2^(x-1)) 1 True) : (listadevalores n (x-1)) 

---
--- Crea distintas listas para luego poder incalar las listas;
--- por ejemplo [True,True,False,False]
---
crearlista::Int->Int->Int->Bool->[Bool]
crearlista n x y b
    |n == y             = [False]
    |(y `mod` x) == 0   = [b] ++ (crearlista n x (y + 1) (not b))
    |otherwise          = [b] ++ (crearlista n x (y + 1) b)

--
-- Funcion para obtener la posicion de un elemento en una lista, si no esta devuelve -1    
--
posicionenlista::Eq a => [a]-> a ->Int
posicionenlista [] a    = -1
posicionenlista l a     = posicionenlista' l a 0
--Funcion auxiliar
posicionenlista'::Eq a => [a]->a->Int->Int
posicionenlista' [] a x = -1
posicionenlista' (l:ls) a x
    |l == a     = x
    |otherwise  = posicionenlista' ls a (x+1)

---
--- Funcion que equivale al si (->) logico
---
siaux::Bool->Bool->Bool
siaux True False    = False
siaux _ _           = True

---
--- Funcion que equivale al si y solo si (<->) logico
---
siiaux::Bool->Bool->Bool
siiaux x y = (x == y)

---
--- Formulas de Ejemplo
---
formula1 = (Si (No (V "p")) (Si (V "p") (Y (V "q") (No (V "q")))))
formula2 = (Y (V "p") (Si (No (V "q")) (No (V "p"))))
formula3 = (Y (V "p") (Y (V "q") (O (No (V "q")) (V "r"))))
formula4 = (Sii (Sii (No (V "a")) (V "a")) (No (Y (No(V "a")) (V "a"))))
formula5 = (No (formula4))
---
--- IO
--- Para probar esta funcionalidad mas facilmente se puede copiar y pegar las formulas de arriba a la consola.
---

--- 
--- Funcion que inicia la interfaz interactiva
--- Pide la primera formula y la pasa a una lista vacia
---
main = do 
    putStrLn "Porfavor introduzca la formula en formato del programa ej. (No (V a))"
    form <- getLine
    preguntarOperacion ((parsear form):[])

---
--- Pregunta que se quiere hacer con la lista de formulas
---
preguntarOperacion::[FProp]->IO ()
preguntarOperacion fs = do
    putStr "Que quiere hacer con las formulas: "
    putStr(show(fs))
    putStrLn " ?"
    putStrLn "1.Es Tautologia? 2.Es Satisfactible? 3.Son Consecuencias? 4. Son Equivalentes?"
    putStrLn "5.añadir otra formula 6.Salir"
    putStrLn "Entrada (1,2,3,4,5 o 6):"
    input <- getChar
    opera fs input

---
--- Parsea un string para convertirlo a un FProp, cuando la entrada tiene algun error devuelve un FPAR = (V error)
--- Esta funcion se hizo antes de saber sobre read.
---
parsear::String->FProp
parsear [] = (V "error")
parsear ('(':str) = parsear (str)
parsear ('V':str) = (V (takeWhile (/=')') str))
parsear ('N':str) = 
    if ((head str) == 'o') 
        then (No (parsear (tail str)))
        else (V "error")
parsear ('Y':str) = (Y (parsear str) (parsear (stringsinprimerparam str 0)))
parsear ('O':str) = (O (parsear str) (parsear (stringsinprimerparam str 0)))
parsear ('S':str) = 
    if ((head str) == 'i') then
        if ((head (tail str)) == 'i')
            then (Sii (parsear str) (parsear (stringsinprimerparam str 0)))
        else 
            (Si (parsear str) (parsear (stringsinprimerparam str 0)))
    else (V "error")
parsear (s:str) = parsear (str)

---
--- Devuelve el string sin el primer parametro de una operacion con dos parametros 
--- Ej: en (Si (V a) (V b)) devuelve (V b))
---
stringsinprimerparam::String->Int->String
stringsinprimerparam [] x = "(V error)"
stringsinprimerparam (')':str) 1 = str
stringsinprimerparam ('(':str) x = stringsinprimerparam str (x+1)
stringsinprimerparam (')':str) x = stringsinprimerparam str (x-1)
stringsinprimerparam (s:str) x = stringsinprimerparam str x

---
--- Opera la diferentes opciones que tiene el programa y imprime el resultado,
--- Y vuelve a preguntar que operacion se quiere hacer
---
opera::[FProp]->Char->IO ()
opera fs '1' = do
    putStrLn (show (map tautologia fs))
    preguntarOperacion fs
opera fs '2' = do
    putStrLn (show (map satisfactible fs))
    preguntarOperacion fs
opera fs '3' = do
    putStrLn (show (consecuencias fs))
    preguntarOperacion fs
opera fs '4' = do
    putStrLn (show (equivalentes fs))
    preguntarOperacion fs
opera fs '5' = do
    putStrLn "Porfavor introduzca la siguiente formula en formato del programa ej. (No (V a))"
    form <- getLine
    preguntarOperacion ((parsear form):fs)
opera fs '6' = do
    putStrLn "Hasta luego!"
opera fs x    = do
    putStrLn "Entrada no valida"
    preguntarOperacion fs