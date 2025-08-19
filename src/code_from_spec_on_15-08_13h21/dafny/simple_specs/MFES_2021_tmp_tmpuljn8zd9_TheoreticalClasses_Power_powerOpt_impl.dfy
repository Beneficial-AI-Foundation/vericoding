function power(x: real, n: nat) : real
{
  if n == 0 then 1.0 else x * power(x, n-1)
}

/* code modified by LLM (iteration 2): added lemma to prove power property for even numbers */
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
    PowerMultiplicationProperty(x, half, half);
  }
}

/* code modified by LLM (iteration 2): added lemma to prove power property for odd numbers */
lemma PowerOddProperty(x: real, n: nat)
  requires n % 2 == 1 && n > 0
  ensures power(x, n) == x * power(x, (n - 1) / 2) * power(x, (n - 1) / 2)
{
  var half := (n - 1) / 2;
  assert n - 1 == 2 * half;
  assert n == 2 * half + 1;
  PowerMultiplicationProperty(x, half, half);
  assert power(x, n - 1) == power(x, half) * power(x, half);
  assert power(x, n) == x * power(x, n - 1);
  assert power(x, n) == x * (power(x, half) * power(x, half));
}

/* code modified by LLM (iteration 2): added lemma to prove multiplication property of power */
lemma PowerMultiplicationProperty(x: real, a: nat, b: nat)
  ensures power(x, a + b) == power(x, a) * power(x, b)
{
  if a == 0 {
    assert power(x, a + b) == power(x, b);
    assert power(x, a) == 1.0;
    assert power(x, a) * power(x, b) == 1.0 * power(x, b) == power(x, b);
  } else {
    PowerMultiplicationProperty(x, a - 1, b);
    assert power(x, (a - 1) + b) == power(x, a - 1) * power(x, b);
    assert power(x, a + b) == x * power(x, (a - 1) + b);
    assert power(x, a + b) == x * power(x, a - 1) * power(x, b);
    assert power(x, a) == x * power(x, a - 1);
    assert power(x, a) * power(x, b) == x * power(x, a - 1) * power(x, b);
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
    /* code modified by LLM (iteration 2): added lemma call to prove even case property */
    PowerEvenProperty(x, n);
    assert half == power(x, n / 2);
    assert power(x, n) == power(x, n / 2) * power(x, n / 2);
    p := half * half;
  } else {
    var half := powerOpt(x, (n - 1) / 2);
    /* code modified by LLM (iteration 2): added lemma call to prove odd case property */
    PowerOddProperty(x, n);
    assert half == power(x, (n - 1) / 2);
    assert power(x, n) == x * power(x, (n - 1) / 2) * power(x, (n - 1) / 2);
    p := x * half * half;
  }
}