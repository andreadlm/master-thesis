import MasterThesis.LOOP.Language

namespace LOOP.func

open LOOP LOOP.Com

/- Somma tra due numeri
   {x = a, y = b, z = 0}
-/
def sum : Com :=
  LOOP "x" (INC "z") ;;
  LOOP "y" (INC "z")
-- {x = a, y = b, z = a + b}

/- Predecessore di un numero
   {x = ?, y = a, z = 0}
-/
def pred : Com :=
  LOOP "y" (
    ZER "x" ;;
    LOOP "z" (INC "x") ;;
    INC "z"
  )
-- {x = a - 1, y = a, z = a}

end LOOP.func
