/* 
* Formal verification of an O(log n) algorithm to calculate the natural power of a real number (x^n), 
* illustrating the usage of lemmas and automatic induction in Dafny.
* J.  Pascoal Faria, FEUP, Jan/2022.
*/

//ATOM power
// Recursive definition of x^n in functional style, with time and space complexity O(n).
function power(x: real, n: nat) : real {
    if n == 0 then 1.0 else x * power(x, n-1)
}

//IMPL powerDC
// Computation of x^n in time and space O(log n).
method powerDC(x: real, n: nat) returns (p : real)
  ensures p == power(x, n)
{
    if n == 0 {
        p := 1.0;
    } else if n == 1 {
        p := x;
    } else if n % 2 == 0 {
        var half := powerDC(x, n / 2);
        /* code modified by LLM (iteration 1): Added lemma call to prove power property for even case */
        productOfPowers(x, n / 2, n / 2);
        /* code modified by LLM (iteration 1): Added assertion to help verification */
        assert n / 2 + n / 2 == n;
        p := half * half;
    } else {
        var half := powerDC(x, n / 2);
        /* code modified by LLM (iteration 1): Added lemma calls to prove power property for odd case */
        productOfPowers(x, n / 2, n / 2);
        productOfPowers(x, n / 2 + n / 2, 1);
        /* code modified by LLM (iteration 1): Added assertion to help verification of odd case arithmetic */
        assert n / 2 + n / 2 + 1 == n;
        p := half * half * x;
    }
}

//IMPL productOfPowers
// States the property x^a * x^b = x^(a+b), that the method power takes advantage of. 
// The property is proved by automatic induction on 'a'.
lemma productOfPowers(x: real, a: nat, b: nat) 
  ensures power(x, a) * power(x, b)  == power(x, a + b) 
{ 
    /* code modified by LLM (iteration 1): Added induction proof structure */
    if a == 0 {
        // Base case: power(x, 0) * power(x, b) == 1.0 * power(x, b) == power(x, b) == power(x, 0 + b)
    } else {
        // Inductive case: use the recursive definition of power
        productOfPowers(x, a - 1, b);
        assert power(x, a) * power(x, b) == (x * power(x, a - 1)) * power(x, b);
        assert (x * power(x, a - 1)) * power(x, b) == x * (power(x, a - 1) * power(x, b));
        assert x * (power(x, a - 1) * power(x, b)) == x * power(x, (a - 1) + b);
        assert x * power(x, (a - 1) + b) == power(x, a + b);
    }
}

//IMPL testPowerDC
// A few test cases (checked statically by Dafny).
method testPowerDC() {
    var p1 := powerDC(2.0, 0);
    assert p1 == 1.0;
    
    var p2 := powerDC(2.0, 1);
    assert p2 == 2.0;
    
    var p3 := powerDC(2.0, 3);
    assert p3 == 8.0;
    
    var p4 := powerDC(3.0, 4);
    assert p4 == 81.0;
    
    var p5 := powerDC(5.0, 2);
    assert p5 == 25.0;
}