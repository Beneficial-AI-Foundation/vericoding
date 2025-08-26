function power(x: real, n: nat) : real {
    if n == 0 then 1.0 else x * power(x, n-1)
}

// Computation of x^n in time and space O(log n).

// <vc-helpers>
lemma powerSquare(x: real, n: nat)
  ensures power(x, n) * power(x, n) == power(x, 2*n)
{
  productOfPowers(x, n, n);
}
// </vc-helpers>

method powerDC(x: real, n: nat) returns (p : real)
  ensures p == power(x, n)
// </vc-spec>
// <vc-code>
{
  if n == 0 {
    p := 1.0;
  }
  else if n % 2 == 0 {
    var half := powerDC(x, n / 2);
    powerSquare(x, n / 2);
    p := half * half;
  }
  else {
    var rest := powerDC(x, n - 1);
    p := x * rest;
  }
}
// </vc-code>

// States the property x^a * x^b = x^(a+b), that the method power takes advantage of. 
// The property is proved by automatic induction on 'a'.
lemma {:induction a} productOfPowers(x: real, a: nat, b: nat) 
  ensures power(x, a) * power(x, b)  == power(x, a + b) 
{ 
    if a == 0 {
        assert power(x, a) * power(x, b) == 1.0 * power(x, b) == power(x, b) == power(x, a + b);
    }
    else {
        // Apply induction hypothesis
        productOfPowers(x, a-1, b);
        // Break down the proof into smaller steps
        calc {
            power(x, a) * power(x, b);
        ==  // definition of power when a > 0
            (x * power(x, a-1)) * power(x, b);
        ==  // associativity of multiplication
            x * (power(x, a-1) * power(x, b));
        ==  // induction hypothesis
            x * power(x, (a-1) + b);
        ==  // arithmetic: (a-1) + b == a + b - 1
            x * power(x, a + b - 1);
        ==  // definition of power when a + b > 0
            power(x, a + b);
        }
    }
}


// A few test cases (checked statically by Dafny).