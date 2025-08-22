/* 
* Formal verification of an O(log n) algorithm to calculate the natural power of a real number (x^n), 
* illustrating the usage of lemmas and automatic induction in Dafny.
* J.  Pascoal Faria, FEUP, Jan/2022.
*/

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
    } else if n % 2 == 1 {
        var temp := powerDC(x, n - 1);
        p := x * temp;
    } else {
        /* code modified by LLM (iteration 1): fixed even case by properly establishing the mathematical relationship */
        var temp := powerDC(x, n / 2);
        productOfPowers(x, n / 2, n / 2);
        assert power(x, n / 2) * power(x, n / 2) == power(x, n / 2 + n / 2);
        assert n / 2 + n / 2 == n;
        assert power(x, n / 2) * power(x, n / 2) == power(x, n);
        assert temp == power(x, n / 2);
        p := temp * temp;
    }
}

// States the property x^a * x^b = x^(a+b), that the method power takes advantage of. 
// The property is proved by automatic induction on 'a'.
lemma productOfPowers(x: real, a: nat, b: nat) 
  ensures power(x, a) * power(x, b)  == power(x, a + b) 
{ }

//IMPL testPowerDC
// A few test cases (checked statically by Dafny).
method testPowerDC() {
    /* code modified by LLM (iteration 1): simplified test cases to rely on postcondition of powerDC */
    var p1 := powerDC(2.0, 0);
    assert p1 == 1.0;
    
    var p2 := powerDC(2.0, 1);
    assert p2 == 2.0;
    
    var p3 := powerDC(2.0, 3);
    proveConcreteValue1();
    assert p3 == 8.0;
    
    var p4 := powerDC(3.0, 4);
    proveConcreteValue2();
    assert p4 == 81.0;
    
    var p5 := powerDC(1.5, 2);
    proveConcreteValue3();
    assert p5 == 2.25;
}

/* code modified by LLM (iteration 1): kept helper lemmas for concrete calculations */
lemma proveConcreteValue1()
  ensures power(2.0, 3) == 8.0
{
    assert power(2.0, 3) == 2.0 * power(2.0, 2);
    assert power(2.0, 2) == 2.0 * power(2.0, 1);
    assert power(2.0, 1) == 2.0 * power(2.0, 0);
    assert power(2.0, 0) == 1.0;
}

lemma proveConcreteValue2()
  ensures power(3.0, 4) == 81.0
{
    assert power(3.0, 4) == 3.0 * power(3.0, 3);
    assert power(3.0, 3) == 3.0 * power(3.0, 2);  
    assert power(3.0, 2) == 3.0 * power(3.0, 1);
    assert power(3.0, 1) == 3.0 * power(3.0, 0);
    assert power(3.0, 0) == 1.0;
}

lemma proveConcreteValue3()
  ensures power(1.5, 2) == 2.25
{
    assert power(1.5, 2) == 1.5 * power(1.5, 1);
    assert power(1.5, 1) == 1.5 * power(1.5, 0);
    assert power(1.5, 0) == 1.0;
}