import MasterThesis.LOOP.Language

namespace LOOP.func

open LOOP LOOP.com

/- Somma tra due numeri
   {x = a, y = b, z = 0}
-/
def sum : com :=
  FOR "x" (INC "z") ;;
  FOR "y" (INC "z")
-- {x = a, y = b, z = a + b}

/- Predecessore di un numero
   {x = ?, y = a, z = 0}
-/
def pred : com :=
  FOR "y" (
    ZER "x" ;;
    FOR "z" (INC "x") ;;
    INC "z"
  )
-- {x = a - 1, y = a, z = a}
end LOOP.func
