//ATOM

// A8Q1 — Steph Renee McIntyre
// Following the solutions from Carmen Bruni

// There is no definition for power, so this function will be used for validating that our imperative program is correct. This is just for Dafny.
function power(a: int, n: int): int //function for a to the power of n
 requires 0 <= n


// SPEC


method A8Q1(y0: int, x: int) returns (z: int)
requires y0 >= 0
/*Post-Condition*/ ensures z==power(x,y0);
{
}

/* Proof of implieds can be seen on LEARN.
  Note: If you are unconvinced, putting asserts for each condition will demonstrate the correctness of the statements. 
*/