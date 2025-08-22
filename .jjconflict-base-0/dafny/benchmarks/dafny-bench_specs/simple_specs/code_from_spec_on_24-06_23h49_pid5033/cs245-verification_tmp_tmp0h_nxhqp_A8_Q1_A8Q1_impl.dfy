//ATOM
// A8Q1 — Steph Renee McIntyre
// Following the solutions from Carmen Bruni

// There is no definition for power, so this function will be used for validating that our imperative program is correct. This is just for Dafny.
function power(a: int, n: int): int //function for a to the power of n
requires 0 <= n
/* code modified by LLM (iteration 1): Added recursive implementation of power function */
{
    if n == 0 then 1
    else a * power(a, n - 1)
}

//IMPL A8Q1
method A8Q1(y0: int, x: int) returns (z: int)
requires y0 >= 0
/*Post-Condition*/ ensures z==power(x,y0);
{
    z := 1;
    var i := 0;
    
    while i < y0
        invariant 0 <= i <= y0
        invariant z == power(x, i)
    {
        /* code modified by LLM (iteration 1): Added assertion to help with verification */
        assert z == power(x, i);
        assert i < y0;
        z := z * x;
        i := i + 1;
        /* code modified by LLM (iteration 1): Added assertion to maintain loop invariant */
        assert z == power(x, i);
    }
}

/* Proof of implieds can be seen on LEARN.
  Note: If you are unconvinced, putting asserts for each condition will demonstrate the correctness of the statements. 
*/