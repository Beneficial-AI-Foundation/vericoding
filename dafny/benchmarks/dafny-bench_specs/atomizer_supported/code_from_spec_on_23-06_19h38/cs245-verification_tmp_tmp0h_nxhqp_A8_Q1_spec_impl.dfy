// A8Q1 — Steph Renee McIntyre
// Following the solutions from Carmen Bruni

// There is no definition for power, so this function will be used for validating that our imperative program is correct. This is just for Dafny.
//ATOM 
function power(a: int, n: int): int //function for a to the power of n
  requires 0 <= n;
{
  if n == 0 then 1
  else a * power(a, n - 1)
}

//IMPL A8Q1
method A8Q1(y0: int, x: int) returns (z: int)
requires y0 >= 0;
/*Post-Condition*/ ensures z==power(x,y0);
{
  var y := y0;
  z := 1;
  
  while y > 0
    invariant 0 <= y <= y0
    invariant z * power(x, y) == power(x, y0)
    decreases y
  {
    z := z * x;
    y := y - 1;
  }
}

/* Proof of implieds can be seen on LEARN.
    Note: If you are unconvinced, putting asserts for each condition will demonstrate the correctness of the statements. 
*/


/* Proof of implieds can be seen on LEARN.
    Note: If you are unconvinced, putting asserts for each condition will demonstrate the correctness of the statements. 
*/



/* Proof of implieds can be seen on LEARN.
    Note: If you are unconvinced, putting asserts for each condition will demonstrate the correctness of the statements. 
*/