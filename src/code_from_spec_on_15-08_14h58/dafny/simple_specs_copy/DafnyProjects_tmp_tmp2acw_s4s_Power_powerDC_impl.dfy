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
    /* code modified by LLM (iteration 1): added assertion to prove even case correctness */
    assert half == power(x, n / 2);
    assert power(x, n) == power(x, n / 2) * power(x, n / 2) by {
      powerEvenLemma(x, n);
    }
    p := half * half;
  } else {
    var half := powerDC(x, (n - 1) / 2);
    /* code modified by LLM (iteration 1): added assertion to prove odd case correctness */
    assert half == power(x, (n - 1) / 2);
    assert power(x, n) == x * power(x, (n - 1) / 2) * power(x, (n - 1) / 2) by {
      powerOddLemma(x, n);
    }
    p := x * half * half;
  }
}

/* code modified by LLM (iteration 1): added helper lemma for even case */
lemma powerEvenLemma(x: real, n: nat)
  requires n > 0 && n % 2 == 0
  ensures power(x, n) == power(x, n / 2) * power(x, n / 2)
{
  var half := n / 2;
  assert n == half + half;
  powerAddLemma(x, half, half);
}

/* code modified by LLM (iteration 1): added helper lemma for odd case */
lemma powerOddLemma(x: real, n: nat)
  requires n > 0 && n % 2 == 1
  ensures power(x, n) == x * power(x, (n - 1) / 2) * power(x, (n - 1) / 2)
{
  var half := (n - 1) / 2;
  assert n == 1 + half + half;
  assert power(x, n) == x * power(x, n - 1);
  powerAddLemma(x, half, half);
  assert power(x, n - 1) == power(x, half) * power(x, half);
}

/* code modified by LLM (iteration 1): added fundamental lemma about power addition */
lemma powerAddLemma(x: real, m: nat, n: nat)
  ensures power(x, m + n) == power(x, m) * power(x, n)
{
  if m == 0 {
    assert power(x, m + n) == power(x, n);
    assert power(x, m) * power(x, n) == 1.0 * power(x, n) == power(x, n);
  } else {
    powerAddLemma(x, m - 1, n);
    assert power(x, (m - 1) + n) == power(x, m - 1) * power(x, n);
    assert power(x, m + n) == power(x, 1 + (m - 1) + n) == x * power(x, (m - 1) + n);
    assert power(x, m + n) == x * power(x, m - 1) * power(x, n);
    assert power(x, m) == x * power(x, m - 1);
    assert power(x, m) * power(x, n) == x * power(x, m - 1) * power(x, n);
  }
}