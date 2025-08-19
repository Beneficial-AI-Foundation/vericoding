function exp(x: real, n: nat) :real
{
  if(n == 0) then 1.0
  else if (x==0.0) then 0.0
  else if (n ==0 && x == 0.0) then 1.0
  else x*exp(x, n-1)
}

//IMPL 

method exp_by_sqr(x0: real, n0: nat) returns (r:real)
requires x0 >= 0.0
ensures r == exp(x0, n0)
{
  var x := x0;
  var n := n0;
  r := 1.0;
  
  while n > 0
    invariant r * exp(x, n) == exp(x0, n0)
    decreases n
  {
    if n % 2 == 1 {
      /* code modified by LLM (iteration 1): added assertion to help prove invariant maintenance */
      assert exp(x, n) == x * exp(x, n-1);
      r := r * x;
      n := n - 1;
      /* code modified by LLM (iteration 1): added assertion to verify invariant after odd case */
      assert r * exp(x, n) == exp(x0, n0);
    } else {
      /* code modified by LLM (iteration 1): added lemma call to prove squaring property */
      exp_squaring_lemma(x, n);
      x := x * x;
      n := n / 2;
      /* code modified by LLM (iteration 1): added assertion to verify invariant after even case */
      assert r * exp(x, n) == exp(x0, n0);
    }
  }
}

/* code modified by LLM (iteration 1): added helper lemma to prove exp(x*x, n/2) == exp(x, n) when n is even */
lemma exp_squaring_lemma(x: real, n: nat)
requires n % 2 == 0
ensures exp(x * x, n / 2) == exp(x, n)
decreases n
{
  if n == 0 {
    // Base case: exp(x*x, 0) == 1.0 == exp(x, 0)
  } else {
    // n > 0 and n is even
    if x == 0.0 {
      // If x == 0, then x*x == 0, and both sides are 0
    } else {
      // Recursive case: prove by induction
      exp_squaring_lemma(x, n - 2);
      assert exp(x, n) == x * exp(x, n-1);
      assert exp(x, n-1) == x * exp(x, n-2);
      assert exp(x, n) == x * x * exp(x, n-2);
      assert exp(x * x, n / 2) == (x * x) * exp(x * x, (n / 2) - 1);
      assert (n / 2) - 1 == (n - 2) / 2;
    }
  }
}