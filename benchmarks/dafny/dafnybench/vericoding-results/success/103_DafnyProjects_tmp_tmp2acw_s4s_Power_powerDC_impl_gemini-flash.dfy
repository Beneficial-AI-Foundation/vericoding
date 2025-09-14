/* 
* Formal verification of an O(log n) algorithm to calculate the natural power of a real number (x^n), 
* illustrating the usage of lemmas and automatic induction in Dafny.
* J.  Pascoal Faria, FEUP, Jan/2022.
*/

// Recursive definition of x^n in functional style, with time and space complexity O(n).
function power(x: real, n: nat) : real {
    if n == 0 then 1.0 else x * power(x, n-1)
}

// Computation of x^n in time and space O(log n).

// <vc-helpers>
lemma lemma_power_multiplication(x: real, a: nat, b: nat)
  ensures power(x, a + b) == power(x, a) * power(x, b)
{
  if a == 0 {
    calc {
      power(x, a + b);
      power(x, b);
      1.0 * power(x, b);
      power(x, a) * power(x, b);
    }
  } else {
    calc {
      power(x, a + b);
      x * power(x, (a - 1) + b);
      { lemma_power_multiplication(x, a - 1, b); } // Recursive call
      x * power(x, a - 1) * power(x, b);
      power(x, a) * power(x, b);
    }
  }
}

lemma reveal_power_multiplication(x: real, a: nat, b: nat)
  ensures power(x, a + b) == power(x, a) * power(x, b)
{
  lemma_power_multiplication(x, a, b);
}

lemma lemma_power_of_product(x: real, m: nat)
  ensures power(x*x, m) == power(x, 2*m)
{
  if m == 0 {
    calc {
      power(x*x, m); power(x*x, 0); 1.0;
      power(x, 0);
      power(x, 2*0);
      power(x, 2*m);
    }
  } else {
    calc {
      power(x*x, m); x*x * power(x*x, m-1);
      { lemma_power_of_product(x, m-1); } // Recursive call
      x*x * power(x, 2*(m-1));
      x*x * power(x, 2*m - 2);
      { lemma_power_multiplication(x, 2*m - 2, 2); }
      power(x, 2*m - 2 + 2);
      power(x, 2*m);
    }
  }
}

lemma reveal_power_of_product(x: real, m: nat)
  ensures power(x*x, m) == power(x, 2*m)
{
  lemma_power_of_product(x, m);
}
// </vc-helpers>

// <vc-spec>
method powerDC(x: real, n: nat) returns (p : real)
  ensures p == power(x, n)
// </vc-spec>
// <vc-code>
{
  if n == 0 {
    p := 1.0;
  } else {
    var half_n := n / 2;
    var p_half := powerDC(x, half_n);
    if n % 2 == 0 {
      p := p_half * p_half;
      calc {
        p_half * p_half;
        power(x, half_n) * power(x, half_n);
        { reveal_power_multiplication(x, half_n, half_n); }
        power(x, half_n + half_n);
        power(x, n);
      }
    } else {
      // n % 2 == 1 && n > 0
      p := x * p_half * p_half;
      calc {
        x * p_half * p_half;
        x * power(x, half_n) * power(x, half_n);
        { reveal_power_multiplication(x, half_n, half_n); }
        x * power(x, half_n + half_n);
        x * power(x, 2*half_n);
        { reveal_power_multiplication(x, 1, 2*half_n); }
        power(x, 1 + 2*half_n);
        power(x, n);
      }
    }
  }
}
// </vc-code>

// A few test cases (checked statically by Dafny).