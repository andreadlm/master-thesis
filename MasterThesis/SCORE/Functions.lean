import MasterThesis.SCORE.Language

namespace SCORE.func

open SCORE SCORE.com

/- Somma tra due numeri
   {x = a, y = b, z = 0} -/
def sum : com :=
  FOR "x" (INC "z") ;;
  FOR "y" (INC "z")
-- {x = a, y = b, z = a + b}

/- Differenza tra due numeri
   {x = a, y = b, z = 0} -/
def diff : com :=
  FOR "x" (INC "z") ;;
  FOR "y" (DEC "z")
-- {x = a, y = b, z = a - b}

/- Prodotto tra due numeri
   {x = a, y = b, z = 0} -/
def prod : com :=
   FOR "y" (
      FOR "x" (INC "z")
   )
-- {x = a, y = b, z = a * b}

def store0 : store := ["x" ↦ [1]] ["y" ↦ [2]] ["z" ↦ [0]]
def store1 : store := ["x" ↦ [-1]] ["y" ↦ [-2]] ["z" ↦ [0]]

end SCORE.func
