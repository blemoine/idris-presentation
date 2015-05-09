Idris
===

Hello World
----
touch hello.idr
idris hello.idr
:e
 
 
 
 ```
 module Main
   
 main : IO()
 main = do putStrLn "Coucou"
 ```

:exec



Les entiers naturels
----

```
data Nat = Z | S Nat

plus : Nat -> Nat -> Nat
plus Z y = y
plus (S k) y = S (plus k y)

```

Typage dépendant - les vecteurs
---

```
data Vect : Nat -> Type -> Type where
  Nil : Vect Z a
  (::) : a -> Vect k a -> Vect (S k) a

instance Show a => Show (Vect n a) where
  show xs = "[" ++ show' xs ++ "]" where
  show' : Vect n a -> String
  show' Nil = ""
  show' (x :: Nil) = show x
  show' (x :: xs) = show x ++ ", " ++ show' xs


main: IO()
main = with Main do
        putStrLn $ show $ ("test" :: Nil)
```

Typage dépendant -  La magie de la completion
---------        

```
concat : Vect n a -> Vect m a -> Vect (n + m) a
```
En se mettant sur concat, shift+alt+/ puis d (\d) -> addclause

```
concat: Vect n a -> Vect m a -> Vect (n + m) a
concat x x1 = ?concat_rhs
```
en se mettnat sur x : \c  -> casesplit

```
concat [] x1 = ?concat_rhs_1
concat (x :: y) x1 = ?concat_rhs_2
```

en se mettant sur ?concat_rhs_1 \p -> proof search
```
concat: Vect n a -> Vect m a -> Vect (n + m) a
concat [] x1 = x1
concat (x :: y) x1 = ?concat_rhs_2
```

en se mettant sur ?concat_rhs_2 \p 

```
concat: Vect n a -> Vect m a -> Vect (n + m) a
concat [] x1 = x1
concat (x :: y) x1 = x :: concat y x1
```

Affichage de concat

```
main: IO()
main = with Main do
        putStrLn $ show $ da
        putStrLn $ show $ (concat da da)
       where
        da : Vect 2 String
        da = "test2" :: "test" :: Nil
```

Meme exemple avec map, mais en rapide

```
map: (a -> b) -> Vect n a -> Vect n b
map f [] = []
map f (x :: y) = f x :: map f y

putStrLn $ show $ map (length) da
```


Finite Set 
----
```
import Data.Fin
// ...

index: Fin n -> Vect n a -> a
```

\d sur index

```
index: Fin n -> Vect n a -> a
index x x1 = ?index_rhs
```

\c sur x puis x1

```
index FZ (x :: y) = ?index_rhs_2
index (FS x) (y :: z) = ?index_rhs_1
```

à la main
```
index: Fin n -> Vect n a -> a
index FZ (x :: y) = x
index (FS x) (y :: z) = index x z

//...

 putStrLn $ show $ (index 1 da)
```

Dependent Pair
----

```
filter: (a -> Bool) -> Vect n a -> (p ** Vect p b)

```
\d + \c

```
filter: (a -> Bool) -> Vect n a -> (p ** Vect p b)
filter f [] = ?filter_rhs_1
filter f (x :: y) = ?filter_rhs_2
```

le \p balance un MkSigma, peu lisible -> à la main

```
filter: (a -> Bool) -> Vect n a -> (p ** Vect p a)
filter f [] = (0 ** [])
filter f (x :: y) with (filter f y)
    | (_ ** xs') = if (f x) then (_ ** x :: xs') else (_ ** xs')
```

et pour afficher :
```
instance Show a => Show (n ** Vect n a) where
    show (n ** xs) = "("++ (show n) ++ "," ++ (show xs) ++ ")"
    
putStrLn $ show $ filter (\x => (length x) == 4) da
```    

Preuves
----

* Refl

 Prouver que 0 est l'élément neutre pour l'addition

```
zeroIsNeutralForPlusLeft: (n:Nat) -> plus Z n = n
```
\d + \p

```
zeroIsNeutralForPlusLeft n = Refl
```

```
zeroIsNeutralForPlusRight: (n:Nat) -> plus n Z = n
```
	
\d + \c + \p

```
zeroIsNeutralForPlusRight: (n:Nat) -> plus n Z = n
zeroIsNeutralForPlusRight Z = Refl
zeroIsNeutralForPlusRight (S k) = ?zeroIsNeutralForPlusRight_rhs_2
```

On va prouver par récurrence

Retour à la console idris

```
:p zeroIsNeutralForPlusRight_rhs_2
intro
intro
rewrite ih
trivial
:addproof
``



TODO : check for totality,
nom des variables générés
%name Vect xs,ys,zs,ws