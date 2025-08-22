/* 
* Formal verification of O(n) and O(log n) algorithms to calculate the natural
* power of a real number (x^n), illustrating the usage of lemmas.
* FEUP, MIEIC, MFES, 2020/21.
*/

//ATOM power
// Initial specification/definition of x^n, recursive, functional style, 
// with time and space complexity O(n).
function power(x: real, n: nat) : real
{
    if n == 0 then 1.0 else x * power(x, n-1)
}

//ATOM powerIter
// Iterative version, imperative, with time complexity O(n) and space complexity O(1).
method powerIter(x: real, n: nat) returns (p: real)
  ensures p == power(x, n)
{
    p := 1.0;
    var i := 0;
    while i < n
      invariant 0 <= i <= n
      invariant p == power(x, i)
    {
        p := p * x;
        i := i + 1;
    }
}

//IMPL powerOpt
// Recursive version, imperative, with time and space complexity O(log n).
method powerOpt(x: real, n: nat) returns (p : real)
  ensures p == power(x, n)
{
    if n == 0 {
        p := 1.0;
    } else if n % 2 == 0 {
        /* code modified by LLM (iteration 1): Fixed recursive call and added proper verification support */
        p := powerOpt(x, n / 2);
        /* code modified by LLM (iteration 1): Added lemma call to establish power property for even numbers */
        powerEvenLemma(x, n);
        p := p * p;
    } else {
        /* code modified by LLM (iteration 1): Fixed recursive call and added proper verification support */
        p := powerOpt(x, n - 1);
        /* code modified by LLM (iteration 1): Added assertion to help with verification */
        assert power(x, n) == x * power(x, n - 1);
        p := x * p;
    }
}

/* code modified by LLM (iteration 1): Added helper lemma for even power case */
lemma powerEvenLemma(x: real, n: nat)
  requires n % 2 == 0
  ensures power(x, n) == power(x, n / 2) * power(x, n / 2)
{
    distributiveProperty(x, n / 2, n / 2);
    assert n / 2 + n / 2 == n;
}

//ATOM distributiveProperty
// States the property x^a * x^b = x^(a+b), that powerOpt takes advantage of. 
// The annotation {:induction a} guides Dafny to prove the property
// by automatic induction on 'a'.
lemma {:induction a} distributiveProperty(x: real, a: nat, b: nat) 
  ensures power(x, a) * power(x, b) == power(x, a + b) 
{
  //    
  // To use the proof below, deactivate automatic induction, with {:induction false}.
   /* if a == 0 {
        // base case
        calc == {
            power(x, a) * power(x, b);
            power(x, 0) * power(x, b); // substitution
            1.0 * power(x, b); // by the definition of power
            power(x, b); // neutral element of "*"
            power(x, a + b); // neutral element of "+"
        }
    }
    else {
        // recursive case, assuming property holds for a-1 (proof by induction)
        distributiveProperty(x, a-1, b); 
        // now do the proof
        calc == {
            power(x, a) * power(x, b);
            (x * power(x, a-1)) * power(x, b); // by the definition of power
            x * (power(x, a-1) * power(x, b)); // associative property
            x * power(x, a + b - 1); // this same property for a-1
            power(x, a + b); // definition of power
        }
    }*/
}

//ATOM testPowerIter
// A simple test case to make sure the specification is adequate.
method testPowerIter()
{
    var result := powerIter(2.0, 3);
    assert result == 8.0;
}

//ATOM testPowerOpt
method testPowerOpt()
{
    var result := powerOpt(2.0, 3);
    assert result == 8.0;
}