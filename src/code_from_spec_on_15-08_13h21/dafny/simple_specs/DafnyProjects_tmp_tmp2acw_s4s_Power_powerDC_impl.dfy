function power(x: real, n: nat) : real {
  if n == 0 then 1.0 else x * power(x, n-1)
}

/* code modified by LLM (iteration 1): Added helper lemma to prove power properties for even numbers */
lemma PowerEvenLemma(x: real, n: nat)
  requires n % 2 == 0 && n > 0
  ensures power(x, n) == power(x, n / 2) * power(x, n / 2)
{
  if n == 2 {
    assert power(x, 2) == x * power(x, 1);
    assert power(x, 1) == x * power(x, 0);
    assert power(x, 0) == 1.0;
    assert power(x, 1) == x * 1.0 == x;
    assert power(x, 2) == x * x;
    assert power(x, n / 2) == power(x, 1) == x;
    assert power(x, n / 2) * power(x, n / 2) == x * x;
  } else {
    var half := n / 2;
    assert n == half + half;
    PowerEvenLemmaHelper(x, half);
  }
}

/* code modified by LLM (iteration 1): Added helper lemma for the inductive case */
lemma PowerEvenLemmaHelper(x: real, k: nat)
  ensures power(x, k + k) == power(x, k) * power(x, k)
{
  if k == 0 {
    assert power(x, 0) == 1.0;
    assert power(x, 0 + 0) == power(x, 0) == 1.0;
    assert power(x, 0) * power(x, 0) == 1.0 * 1.0 == 1.0;
  } else {
    PowerEvenLemmaHelper(x, k - 1);
    assert power(x, (k-1) + (k-1)) == power(x, k-1) * power(x, k-1);
    assert power(x, k) == x * power(x, k-1);
    assert power(x, k + k) == x * power(x, k + k - 1);
    assert k + k - 1 == (k-1) + k;
    assert power(x, (k-1) + k) == x * power(x, (k-1) + k - 1);
    assert (k-1) + k - 1 == (k-1) + (k-1);
  }
}

/* code modified by LLM (iteration 1): Added helper lemma for odd numbers */
lemma PowerOddLemma(x: real, n: nat)
  requires n % 2 == 1 && n > 0
  ensures power(x, n) == x * power(x, (n-1)/2) * power(x, (n-1)/2)
{
  var k := (n - 1) / 2;
  assert n == 2 * k + 1;
  assert power(x, n) == x * power(x, n - 1);
  assert n - 1 == 2 * k;
  PowerEvenLemmaHelper(x, k);
  assert power(x, 2 * k) == power(x, k) * power(x, k);
  assert power(x, n) == x * power(x, k) * power(x, k);
}


//IMPL 

// Computation of x^n in time and space O(log n).
method powerDC(x: real, n: nat) returns (p : real)
 ensures p == power(x, n)
{
  if n == 0 {
    p := 1.0;
  } else if n % 2 == 0 {
    /* code modified by LLM (iteration 1): Added lemma call and assertion */
    PowerEvenLemma(x, n);
    var half := powerDC(x, n / 2);
    assert half == power(x, n / 2);
    p := half * half;
    assert p == power(x, n / 2) * power(x, n / 2);
    assert p == power(x, n);
  } else {
    /* code modified by LLM (iteration 1): Added lemma call and assertion */
    PowerOddLemma(x, n);
    var half := powerDC(x, (n - 1) / 2);
    assert half == power(x, (n - 1) / 2);
    p := x * half * half;
    assert p == x * power(x, (n - 1) / 2) * power(x, (n - 1) / 2);
    assert p == power(x, n);
  }
}