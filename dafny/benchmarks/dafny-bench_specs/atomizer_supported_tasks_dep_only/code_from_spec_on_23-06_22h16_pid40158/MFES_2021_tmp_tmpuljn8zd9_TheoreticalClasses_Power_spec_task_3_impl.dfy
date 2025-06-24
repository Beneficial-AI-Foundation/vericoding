/* 
* Formal verification of O(n) and O(log n) algorithms to calculate the natural
* power of a real number (x^n), illustrating the usage of lemmas.
* FEUP, MIEIC, MFES, 2020/21.
*/

// Initial specification/definition of x^n, recursive, functional style, 
// with time and space complexity O(n).
//ATOM power
function power(x: real, n: nat) : real
{
    if n == 0 then 1.0 else x * power(x, n-1)
}

//IMPL powerIter
method powerIter(x: real, n: nat) returns (p : real)
  ensures p == power(x, n)
{
    p := 1.0;
    var i := 0;
    while i < n
        invariant 0 <= i <= n
        invariant p == power(x, i)
    {
        /* code modified by LLM (iteration 1): added lemma call to establish the power relationship */
        powerStepLemma(x, i);
        p := p * x;
        i := i + 1;
    }
}

/* code modified by LLM (iteration 1): added helper lemma to prove power step relationship */
lemma powerStepLemma(x: real, i: nat)
  ensures power(x, i + 1) == x * power(x, i)
{
    // This follows directly from the definition of power
}

//ATOM distributiveProperty
lemma distributiveProperty(x: real, a: nat, b: nat) 
  ensures power(x, a) * power(x, b)  == power(x, a + b) 
{
}

//IMPL testPowerIter
method testPowerIter()
{
    /* code modified by LLM (iteration 1): added proper method body with variable declaration */
    var result := powerIter(2.0, 3);
    assert result == power(2.0, 3);
}