/* 
* Formal verification of an O(log n) algorithm to calculate the natural power of a real number (x^n), 
* illustrating the usage of lemmas and automatic induction in Dafny.
* J.  Pascoal Faria, FEUP, Jan/2022.
*/

// Recursive definition of x^n in functional style, with time and space complexity O(n).
//ATOM 
function power(x: real, n: nat) : real {
    if n == 0 then 1.0 else x * power(x, n-1)
}

//IMPL 
// Computation of x^n in time and space O(log n).
method powerDC(x: real, n: nat) returns (p : real)
  ensures p == power(x, n)
{
    if n == 0 {
        p := 1.0;
    } else if n % 2 == 0 {
        var half := powerDC(x, n / 2);
        productOfPowers(x, n / 2, n / 2);
        p := half * half;
    } else {
        var half := powerDC(x, n / 2);
        /* code modified by LLM (iteration 1): fixed mathematical reasoning for odd n case */
        // For odd n: n = 2*(n/2) + 1, so x^n = x^(2*(n/2) + 1) = x^(2*(n/2)) * x^1
        // We know half == power(x, n/2)
        // So half * half == power(x, n/2) * power(x, n/2)
        
        // Apply productOfPowers to get: power(x, n/2) * power(x, n/2) == power(x, n/2 + n/2)
        productOfPowers(x, n / 2, n / 2);
        assert half * half == power(x, n / 2 + n / 2);
        assert power(x, n / 2 + n / 2) == power(x, 2 * (n / 2));
        
        // For odd n, we have n = 2*(n/2) + 1
        assert n == 2 * (n / 2) + 1;
        
        // Now apply productOfPowers again: power(x, 2*(n/2)) * power(x, 1) == power(x, 2*(n/2) + 1)
        productOfPowers(x, 2 * (n / 2), 1);
        assert power(x, 2 * (n / 2)) * power(x, 1) == power(x, 2 * (n / 2) + 1);
        assert power(x, 2 * (n / 2) + 1) == power(x, n);
        assert power(x, 1) == x;
        
        p := half * half * x;
    }
}

// States the property x^a * x^b = x^(a+b), that the method power takes advantage of. 
// The property is proved by automatic induction on 'a'.
//ATOM 
lemma productOfPowers(x: real, a: nat, b: nat) 
  ensures power(x, a) * power(x, b)  == power(x, a + b) 
{ }

// A few test cases (checked statically by Dafny).
//ATOM 
method testPowerDC() {
    var p;
    p := powerDC(2.0, 0);
    assert p == 1.0;
    p := powerDC(2.0, 1);
    assert p == 2.0;
    p := powerDC(2.0, 2);
    assert p == 4.0;
    p := powerDC(2.0, 3);
    assert p == 8.0;
    p := powerDC(3.0, 4);
    assert p == 81.0;
}