function power(x: real, n: nat) : real
{
  if n == 0 then 1.0 else x * power(x, n-1)
}

/* code modified by LLM (iteration 2): Added helper lemma to prove power property for even numbers */
lemma PowerEvenProperty(x: real, n: nat)
  requires n % 2 == 0 && n > 0
  ensures power(x, n) == power(x, n / 2) * power(x, n / 2)
{
  if n == 2 {
    // Base case: power(x, 2) == x * x == power(x, 1) * power(x, 1)
    assert power(x, 2) == x * power(x, 1);
    assert power(x, 1) == x;
    assert power(x, 2) == x * x;
    assert power(x, n / 2) == power(x, 1) == x;
  } else {
    // Inductive case
    var half := n / 2;
    assert n == 2 * half;
    PowerMultiplicativeProperty(x, half, half);
  }
}

/* code modified by LLM (iteration 2): Added helper lemma to prove power property for odd numbers */
lemma PowerOddProperty(x: real, n: nat)
  requires n % 2 == 1 && n > 0
  ensures power(x, n) == x * power(x, (n - 1) / 2) * power(x, (n - 1) / 2)
{
  var half := (n - 1) / 2;
  assert n - 1 == 2 * half;
  assert n == 2 * half + 1;
  PowerMultiplicativeProperty(x, half, half);
  assert power(x, n - 1) == power(x, half) * power(x, half);
  assert power(x, n) == x * power(x, n - 1);
}

/* code modified by LLM (iteration 2): Added fundamental lemma about power multiplication */
lemma PowerMultiplicativeProperty(x: real, m: nat, n: nat)
  ensures power(x, m + n) == power(x, m) * power(x, n)
{
  if m == 0 {
    assert power(x, m + n) == power(x, n);
    assert power(x, m) == 1.0;
  } else {
    PowerMultiplicativeProperty(x, m - 1, n);
    assert power(x, (m - 1) + n) == power(x, m - 1) * power(x, n);
    assert power(x, m + n) == x * power(x, (m + n) - 1);
    assert power(x, m + n) == x * power(x, (m - 1) + n);
    assert power(x, m + n) == x * power(x, m - 1) * power(x, n);
    assert power(x, m) == x * power(x, m - 1);
  }
}

//IMPL 

// Recursive version, imperative, with time and space complexity O(log n).
method powerOpt(x: real, n: nat) returns (p : real)
 ensures p == power(x, n)
{
  if n == 0 {
    p := 1.0;
  } else if n % 2 == 0 {
    var half := powerOpt(x, n / 2);
    /* code modified by LLM (iteration 2): Added lemma call to prove the assertion */
    PowerEvenProperty(x, n);
    assert power(x, n) == power(x, n / 2) * power(x, n / 2);
    p := half * half;
  } else {
    var half := powerOpt(x, (n - 1) / 2);
    /* code modified by LLM (iteration 2): Added lemma call to prove the assertion */
    PowerOddProperty(x, n);
    assert power(x, n) == x * power(x, (n - 1) / 2) * power(x, (n - 1) / 2);
    p := x * half * half;
  }
}