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

//IMPL powerOpt
// Recursive version, imperative, with time and space complexity O(log n).
method powerOpt(x: real, n: nat) returns (p : real)
  ensures p == power(x, n);
{
    if n == 0 {
        p := 1.0;
    } else if n % 2 == 0 {
        var half := powerOpt(x, n / 2);
        /* code modified by LLM (iteration 2): Added proper verification for even case using distributive property */
        distributiveProperty(x, n / 2, n / 2);
        p := half * half;
    } else {
        var rest := powerOpt(x, n - 1);
        /* code modified by LLM (iteration 2): Added proper verification for odd case using distributive property */
        distributiveProperty(x, 1, n - 1);
        p := x * rest;
    }
}

//IMPL testPowerOpt
method testPowerOpt(){
    var result := powerOpt(2.0, 3);
    /* code modified by LLM (iteration 2): Simplified test verification by relying on powerOpt postcondition */
    assert result == power(2.0, 3);
    assert power(2.0, 3) == 2.0 * power(2.0, 2);
    assert power(2.0, 2) == 2.0 * power(2.0, 1);  
    assert power(2.0, 1) == 2.0 * power(2.0, 0);
    assert power(2.0, 0) == 1.0;
    assert result == 8.0;
}