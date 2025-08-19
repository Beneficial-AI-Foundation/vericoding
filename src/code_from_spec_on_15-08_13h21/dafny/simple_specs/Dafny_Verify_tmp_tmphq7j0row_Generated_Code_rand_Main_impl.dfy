//IMPL
/* code modified by LLM (iteration 2): renamed method from Main to MultiplyToZero to fix compilation error - Dafny Main method cannot have multiple parameters */
method MultiplyToZero(xInit: int, y: int) returns (z: int)
 requires xInit >= 0
 requires y >= 0
 ensures z == 0
{
 var x := xInit;
 z := x * y;
 
 while x > 0
  invariant z == x * y
  invariant x >= 0
 {
  x := x - 1;
  z := z - y;
 }
}