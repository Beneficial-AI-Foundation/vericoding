//ATOM
// A8Q1 — Steph Renee McIntyre
// Following the solutions from Carmen Bruni

// There is no definition for power, so this function will be used for validating that our imperative program is correct. This is just for Dafny.
function power(a: int, n: int): int //function for a to the power of n
 requires 0 <= n
{
    if n == 0 then 1 else a * power(a, n - 1)
}

//IMPL A8Q1
method A8Q1(y0: int, x: int) returns (z: int)
requires y0 >= 0
ensures z==power(x,y0)
{
    z := 1;
    var i := 0;
    
    while i < y0
        invariant 0 <= i <= y0
        /* code modified by LLM (iteration 1): invariant connecting z with power function */
        invariant z == power(x, i)
    {
        /* code modified by LLM (iteration 1): added assertion to help prove invariant maintenance */
        assert z == power(x, i);
        assert power(x, i + 1) == x * power(x, i);
        z := z * x;
        i := i + 1;
        /* code modified by LLM (iteration 1): assertion to verify invariant after updates */
        assert z == power(x, i);
    }
}

/* code modified by LLM (iteration 1): removed helper lemma as power function now has proper definition */

/* Proof of implieds can be seen on LEARN.
  Note: If you are unconvinced, putting asserts for each condition will demonstrate the correctness of the statements. 
*/