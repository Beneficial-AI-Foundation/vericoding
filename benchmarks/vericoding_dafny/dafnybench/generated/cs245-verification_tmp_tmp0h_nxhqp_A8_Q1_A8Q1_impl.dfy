// A8Q1 — Steph Renee McIntyre
// Following the solutions from Carmen Bruni

// There is no definition for power, so this function will be used for validating that our imperative program is correct. This is just for Dafny.
// <vc-spec>
function power(a: int, n: int): int //function for a to the power of n
  requires 0 <= n
  decreases n
  {
    if (n == 0) then 1 else a * power(a, n - 1)
  }

// <vc-helpers>
lemma PowerMultiplicative(a: int, m: int, n: int)
  requires 0 <= m && 0 <= n
  ensures power(a, m + n) == power(a, m) * power(a, n)
  decreases m
{
  if m == 0 {
    // power(a, 0 + n) == power(a, n) == 1 * power(a, n) == power(a, 0) * power(a, n)
  } else {
    // power(a, m + n) == a * power(a, (m-1) + n)
    // By induction: power(a, (m-1) + n) == power(a, m-1) * power(a, n)
    // So: power(a, m + n) == a * power(a, m-1) * power(a, n) == power(a, m) * power(a, n)
    PowerMultiplicative(a, m - 1, n);
  }
}

lemma PowerSquare(a: int, n: int)
  requires 0 <= n
  ensures power(a * a, n) == power(a, 2 * n)
  decreases n
{
  if n == 0 {
    // power(a * a, 0) == 1 == power(a, 0)
  } else {
    // power(a * a, n) == (a * a) * power(a * a, n - 1)
    // By induction: power(a * a, n - 1) == power(a, 2 * (n - 1))
    // So: power(a * a, n) == (a * a) * power(a, 2 * (n - 1))
    //                     == (a * a) * power(a, 2 * n - 2)
    //                     == a * a * power(a, 2 * n - 2)
    //                     == a * (a * power(a, 2 * n - 2))
    //                     == a * power(a, 2 * n - 1)
    //                     == power(a, 2 * n)
    PowerSquare(a, n - 1);
    PowerMultiplicative(a, 1, 2 * n - 1);
  }
}
// </vc-helpers>

method A8Q1(y0: int, x: int) returns (z: int)
requires y0 >= 0
ensures z==power(x,y0)
// </vc-spec>
// <vc-code>
{
  var result := 1;
  var base := x;
  var exponent := y0;
  
  while exponent > 0
    invariant 0 <= exponent <= y0
    invariant result * power(base, exponent) == power(x, y0)
    decreases exponent
  {
    if exponent % 2 == 1 {
      result := result * base;
      exponent := exponent - 1;
      // Need to prove that new_result * power(base, new_exponent) == power(x, y0)
      // new_result = result * base, new_exponent = exponent - 1
      // new_result * power(base, new_exponent) = (result * base) * power(base, exponent - 1)
      //                                        = result * (base * power(base, exponent - 1))
      //                                        = result * power(base, exponent)
      //                                        = power(x, y0)
    } else {
      // exponent is even and > 0, so exponent >= 2
      assert exponent % 2 == 0;
      assert exponent == 2 * (exponent / 2);
      PowerSquare(base, exponent / 2);
      base := base * base;
      exponent := exponent / 2;
      // Need to prove that result * power(new_base, new_exponent) == power(x, y0)
      // new_base = base * base, new_exponent = exponent / 2
      // Since exponent is even, exponent = 2 * (exponent / 2)
      // result * power(new_base, new_exponent) = result * power(base * base, exponent / 2)
      //                                        = result * power(base, 2 * (exponent / 2))
      //                                        = result * power(base, exponent)
      //                                        = power(x, y0)
    }
  }
  
  z := result;
}
// </vc-code>

/* Proof of implieds can be seen on LEARN.
    Note: If you are unconvinced, putting asserts for each condition will demonstrate the correctness of the statements. 
*/