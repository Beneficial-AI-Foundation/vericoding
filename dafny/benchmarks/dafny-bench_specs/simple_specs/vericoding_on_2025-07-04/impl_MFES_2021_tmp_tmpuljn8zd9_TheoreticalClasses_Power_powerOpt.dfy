//ATOM

// Initial specification/definition of x^n, recursive, functional style, 
// with time and space complexity O(n).
function power(x: real, n: nat) : real
{
  if n == 0 then 1.0 else x * power(x, n-1)
}

//IMPL 

/* code modified by LLM (iteration 1): Added helper lemmas to prove mathematical properties of exponentiation */
lemma PowerSquare(x: real, n: nat)
  ensures power(x, 2 * n) == power(x, n) * power(x, n)
{
  if n == 0 {
    // Base case: power(x, 0) == 1.0
  } else {
    // Inductive case
    calc {
      power(x, 2 * n);
      == power(x, n + n);
      == { PowerAdditive(x, n, n); }
      power(x, n) * power(x, n);
    }
  }
}

lemma PowerAdditive(x: real, m: nat, n: nat)
  ensures power(x, m + n) == power(x, m) * power(x, n)
{
  if m == 0 {
    // Base case
  } else {
    calc {
      power(x, m + n);
      == x * power(x, (m - 1) + n);
      == { PowerAdditive(x, m - 1, n); }
      x * power(x, m - 1) * power(x, n);
      == x * power(x, m - 1) * power(x, n);
      == power(x, m) * power(x, n);
    }
  }
}

lemma PowerOddCase(x: real, n: nat)
  requires n % 2 == 1 && n > 0
  ensures power(x, n) == x * power(x, (n - 1) / 2) * power(x, (n - 1) / 2)
{
  var k := (n - 1) / 2;
  assert n == 2 * k + 1;
  calc {
    power(x, n);
    == power(x, 2 * k + 1);
    == x * power(x, 2 * k);
    == { PowerSquare(x, k); }
    x * power(x, k) * power(x, k);
  }
}

// Recursive version, imperative, with time and space complexity O(log n).
method powerOpt(x: real, n: nat) returns (p : real)
 ensures p == power(x, n)
{
  if n == 0 {
    p := 1.0;
  } else if n % 2 == 0 {
    var half := powerOpt(x, n / 2);
    /* code modified by LLM (iteration 1): Added lemma call to prove even case correctness */
    PowerSquare(x, n / 2);
    p := half * half;
  } else {
    var half := powerOpt(x, (n - 1) / 2);
    /* code modified by LLM (iteration 1): Added lemma call to prove odd case correctness */
    PowerOddCase(x, n);
    p := x * half * half;
  }
}