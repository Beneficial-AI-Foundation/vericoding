//ATOM

// Recursive definition of x^n in functional style, with time and space complexity O(n).
function power(x: real, n: nat) : real {
  if n == 0 then 1.0 else x * power(x, n-1)
}

/* code modified by LLM (iteration 1): Added helper lemmas to prove mathematical properties of exponentiation */
lemma PowerAdditive(x: real, m: nat, n: nat)
  ensures power(x, m + n) == power(x, m) * power(x, n)
{
  if m == 0 {
    // Base case: power(x, 0 + n) == 1.0 * power(x, n) == power(x, n)
  } else {
    // Inductive case: power(x, (m-1) + 1 + n) == power(x, (m-1) + (1 + n))
    PowerAdditive(x, m - 1, n + 1);
    // power(x, m + n) == x * power(x, m - 1 + n) == x * power(x, m - 1) * power(x, n) == power(x, m) * power(x, n)
  }
}

lemma PowerDouble(x: real, n: nat)
  ensures power(x, 2 * n) == power(x, n) * power(x, n)
{
  PowerAdditive(x, n, n);
}

lemma PowerOddDecomposition(x: real, n: nat)
  requires n > 0
  ensures power(x, n) == x * power(x, n - 1)
{
  // This follows directly from the definition of power
}

//IMPL 

// Computation of x^n in time and space O(log n).
method powerDC(x: real, n: nat) returns (p : real)
 ensures p == power(x, n)
{
  if n == 0 {
    p := 1.0;
  } else if n % 2 == 0 {
    /* code modified by LLM (iteration 1): Added lemma call to prove correctness for even case */
    PowerDouble(x, n / 2);
    var half := powerDC(x, n / 2);
    p := half * half;
  } else {
    /* code modified by LLM (iteration 1): Added lemma calls to prove correctness for odd case */
    PowerOddDecomposition(x, n);
    PowerDouble(x, (n - 1) / 2);
    var half := powerDC(x, (n - 1) / 2);
    p := x * half * half;
  }
}