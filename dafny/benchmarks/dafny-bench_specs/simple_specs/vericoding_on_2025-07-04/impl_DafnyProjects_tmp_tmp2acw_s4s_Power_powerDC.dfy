//ATOM

// Recursive definition of x^n in functional style, with time and space complexity O(n).
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
    /* code modified by LLM (iteration 1): Call helper lemma and use the correct relationship */
    PowerEvenLemma(x, n);
    p := half * half;
  } else {
    var half := powerDC(x, (n - 1) / 2);
    /* code modified by LLM (iteration 1): Call helper lemma and use the correct relationship */
    PowerOddLemma(x, n);
    p := x * half * half;
  }
}

/* code modified by LLM (iteration 1): Fixed lemma to prove the correct property for even exponents */
lemma PowerEvenLemma(x: real, n: nat)
  requires n % 2 == 0 && n > 0
  ensures power(x, n) == power(x, n / 2) * power(x, n / 2)
{
  var half := n / 2;
  assert n == 2 * half;
  PowerDoubleHelper(x, half);
}

/* code modified by LLM (iteration 1): Helper lemma to prove x^(2k) = x^k * x^k */
lemma PowerDoubleHelper(x: real, k: nat)
  ensures power(x, 2 * k) == power(x, k) * power(x, k)
{
  if k == 0 {
    // Base case: power(x, 0) = 1, so power(x, 0) * power(x, 0) = 1 * 1 = 1 = power(x, 0)
  } else {
    // Inductive step
    calc {
      power(x, 2 * k);
      == x * power(x, 2 * k - 1);
      == x * x * power(x, 2 * k - 2);
      == x * x * power(x, 2 * (k - 1));
      == { PowerDoubleHelper(x, k - 1); }
         x * x * power(x, k - 1) * power(x, k - 1);
      == x * power(x, k - 1) * x * power(x, k - 1);
      == power(x, k) * power(x, k);
    }
  }
}

/* code modified by LLM (iteration 1): Fixed lemma to prove the correct property for odd exponents */
lemma PowerOddLemma(x: real, n: nat)
  requires n % 2 == 1 && n > 0
  ensures power(x, n) == x * power(x, (n - 1) / 2) * power(x, (n - 1) / 2)
{
  var half := (n - 1) / 2;
  assert n == 2 * half + 1;
  PowerDoubleHelper(x, half);
  calc {
    power(x, n);
    == power(x, 2 * half + 1);
    == x * power(x, 2 * half);
    == { PowerDoubleHelper(x, half); }
       x * power(x, half) * power(x, half);
  }
}