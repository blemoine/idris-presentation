DEMO AVEC MATRIX ?
===

- Montrer les vecteurs dans la prez

hello world
----
  
   ```
touch hello.idr
idris hello.idr
:e
   ```
 
```
 module Main
   
 main : IO()
 main = do putStrLn "Coucou"
```

:exec

type Matrix
---

```
import Data.Vect

Matrix: Nat -> Nat -> Type -> Type
Matrix n m a = Vect n (Vect m a)

main:IO()
main = do
  printLn "Hello"
  printLn m
 where
  m:Matrix 2 3 Nat
  m = [[1,2,3], [4, 5, 6]]
```

   * comment construire un type à partir d'une fonction
   * montrer le ```where```
   * montrer que si je ne met pas les bonnes dimensions pour ma matric ca compile pas
 

Addition sur le type Matrix
---

```
add: (Num a) => Matrix n m a -> Matrix n m a -> Matrix n m a
```

\d

```
add x x1 = ?add_rhs
```

\c \c \c \c

```
add [] [] = ?add_rhs_2
add (x :: xs) (y :: ys) = ?add_rhs_1
```

\o

```
add [] [] = []
add (x :: xs) (y :: ys) = ?add_rhs_1
```

```
add (x :: xs) (y :: ys) = (zipWith (+) x y) :: add xs ys
printLn (add m m)
```


 * génération de code quand possible
 * fonction anonyme
 * contrainte sur Num
 

Récupérer un élément de la matrice
---

```
import Data.Fin

idx: Fin n -> Fin m -> Matrix n m a -> a
idx x x1 x2 = index x1 (index x x2)

 printLn $ (idx 1 2 m)
```

 * montrer Fin n
 * montrer que ca compile pas si n ou m > 


Hauteur et Largeur
---

```
height: Matrix n m a -> Nat
height matrix = length matrix

width: Matrix n m a -> Nat
width {m} xs = m
```

  * cas simple de hauteur, rien à dire
  * largeur généré introduit m -> accés aux paramètres implicites
  
Dependent pair - filterRow
---

```
filterRow: (Vect m a -> Bool) ->  Matrix n m a -> Matrix p m a
filterRow f [] = []
filterRow f (x :: xs) = ?filterRow_rhs_2
```

Ne compile pas => passage en dependent pair

```
filterRow: (Vect m a -> Bool) ->  Matrix n m a -> (p ** Matrix p m a)
filterRow f [] = (0 ** [])
filterRow f (x :: xs) with (filterRow f xs)
  | (_ ** tail) = if (f x) then (_ ** x :: tail) else (_ ** tail)

instance Show a => Show (p ** Matrix p m a) where
  show (p ** m) = show m
  
printLn $ filterRow (\v => head v < 2) m
```

  * Pair dépendante => "il existe"
  * Type Classe



Preuves directes
---

```
total
heightCorrect: (n:Nat) -> (mat:Matrix n m a) -> height mat = n
heightCorrect Z [] = Refl
heightCorrect (S k) (x :: xs) = rewrite heightCorrect k xs in Refl
```


 * Concept de preuve
 * Refl
 * rewrite
 
 
Preuves par tactiques
---

```
total
zeroVectIsNeutralForAddLeft: (v: Vect n Nat) -> (zipWith (+) (replicate n 0) v) = v
zeroVectIsNeutralForAddLeft [] = Refl
zeroVectIsNeutralForAddLeft (x :: xs) = let ih = zeroVectIsNeutralForAddLeft xs in ?zeroVectIsNeutralForAddLeft_rhs_3
```

:p zeroVectIsNeutralForAddLeft_rhs_3

intros
rewrite sym ih
rewrite sym ih
trivial
qed

:addproof

équivalent à

```
zeroVectIsNeutralForAddLeft (x :: xs) = rewrite sym (zeroVectIsNeutralForAddLeft xs) in Refl
```








