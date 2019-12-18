module Main

import Data.Vect

id: a -> a
id x = x

map: (a -> b) -> Vect n a -> Vect n b
map f [] = []
map f (x :: xs) = ?map_rhs_2



main : IO ()
main = putStrLn "Hello world dadada"
       
