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
lemma PowerEven(x: real, n: nat)
  ensures power(x, 2*n) == power(x, n) * power(x, n)
{
  if n == 0 {
  } else {
    PowerEven(x, n-1);
    calc {
      power(x, 2*n);
      == x * power(x, 2*n - 1);
      == x * (x * power(x, 2*n - 2));
      == x * x * power(x, 2*(n-1));
      == { PowerEven(x, n-1); } x * x * (power(x, n-1) * power(x, n-1));
      == { assert power(x, n) == x * power(x, n-1); } x * x * power(x, n-1) * power(x, n-1);
      == (x * power(x, n-1)) * (x * power(x, n-1));
      == power(x, n) * power(x, n);
    }
  }
}

lemma PowerOdd(x: real, n: nat)
  ensures power(x, 2*n + 1) == x * power(x, n) * power(x, n)
{
  if n == 0 {
  } else {
    PowerEven(x, n);
    calc {
      power(x, 2*n + 1);
      == x * power(x, 2*n);
      == { PowerEven(x, n); } x * (power(x, n) * power(x, n));
    }
    calc {
      x * power(x, n) * power(x, n);
      == x * power(x, n) * power(x, n);
    }
  }
}

lemma PowerSquare(x: real, half: nat)
  ensures power(x*x, half) == power(x, 2*half)
{
  if half == 0 {
  } else {
    PowerSquare(x, half-1);
    calc {
      power(x*x, half);
      == x*x * power(x*x, half-1);
      == { PowerSquare(x, half-1); } x*x * power(x, 2*(half-1));
    }
    calc {
      power(x, 2*half);
      == x * power(x, 2*half - 1);
      == x * power(x, 2*(half-1) + 1);
      == x * (x * power(x, 2*(half-1)));
      == x*x * power(x, 2*(half-1));
    }
  }
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
  } else if n % 2 == 0 {
    var half := powerDC(x, n / 2);
    calc {
      half * half;
      == power(x, n / 2) * power(x, n / 2);
      == { PowerEven(x, n / 2); } power(x, 2 * (n / 2));
      == power(x, n);
    }
    p := half * half;
  } else {
    var half := powerDC(x, (n - 1) / 2);
    calc {
      half * half * x;
      == power(x, (n - 1) / 2) * power(x, (n - 1) / 2) * x;
      == { PowerOdd(x, (n - 1) / 2); } power(x, 2 * ((n - 1) / 2) + 1);
      == power(x, n);
    }
    p := half * half * x;
  }
}
// </vc-code>

// A few test cases (checked statically by Dafny).