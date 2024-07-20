import MasterThesis.SCORE.Language

namespace SCORE.func

open SCORE SCORE.Com

/- Somma tra due numeri
   {x = a, y = b, z = 0} -/
def sum : Com :=
  FOR "x" (INC "z") ;;
  FOR "y" (INC "z")
-- {x = a, y = b, z = a + b}

/- Differenza tra due numeri
   {x = a, y = b, z = 0} -/
def diff : Com :=
  FOR "x" (INC "z") ;;
  FOR "y" (DEC "z")
-- {x = a, y = b, z = a - b}

/- Prodotto tra due numeri
   {x = a, y = b, z = 0} -/
def prod : Com :=
   FOR "y" (
      FOR "x" (INC "z")
   )
-- {x = a, y = b, z = a * b}

end SCORE.func
