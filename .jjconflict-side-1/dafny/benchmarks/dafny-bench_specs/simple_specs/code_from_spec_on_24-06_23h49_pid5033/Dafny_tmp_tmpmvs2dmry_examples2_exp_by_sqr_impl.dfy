//ATOM

function exp(x: real, n: nat) :real
{
  if(n == 0) then 1.0
  else if (x==0.0) then 0.0
  else if (n ==0 && x == 0.0) then 1.0
  else x*exp(x, n-1)
}

//IMPL exp_by_sqr

method exp_by_sqr(x0: real, n0: nat) returns (r:real)
requires x0 >= 0.0
ensures r == exp(x0, n0)
{
  var x := x0;
  var n := n0;
  r := 1.0;
  
  while n > 0
    invariant r * exp(x, n) == exp(x0, n0)
    invariant x >= 0.0
    decreases n
  {
    if n % 2 == 1 {
      r := r * x;
      n := n - 1;
    } else {
      /* code modified by LLM (iteration 2): Call helper lemma to establish the squaring property */
      exp_square_lemma(x, n);
      x := x * x;
      n := n / 2;
    }
  }
}

/* code modified by LLM (iteration 2): Simplified and corrected helper lemma using strong induction */
lemma exp_square_lemma(x: real, n: nat)
requires n % 2 == 0 && n > 0
ensures exp(x, n) == exp(x * x, n / 2)
decreases n
{
  if n == 2 {
    calc {
      exp(x, 2);
      == x * exp(x, 1);
      == x * (x * exp(x, 0));
      == x * (x * 1.0);
      == x * x;
      == (x * x) * 1.0;
      == (x * x) * exp(x * x, 0);
      == exp(x * x, 1);
    }
  } else {
    var half := n / 2;
    assert n == 2 * half;
    assert half > 1;
    
    calc {
      exp(x, n);
      == exp(x, 2 * half);
      == { exp_double_lemma(x, half); }
      exp(x * x, half);
    }
  }
}

/* code modified by LLM (iteration 2): Added lemma to prove x^(2k) = (x²)^k */
lemma exp_double_lemma(x: real, k: nat)
requires k >= 1
ensures exp(x, 2 * k) == exp(x * x, k)
decreases k
{
  if k == 1 {
    calc {
      exp(x, 2);
      == x * exp(x, 1);
      == x * (x * exp(x, 0));
      == x * x * 1.0;
      == (x * x) * 1.0;
      == (x * x) * exp(x * x, 0);
      == exp(x * x, 1);
    }
  } else {
    calc {
      exp(x, 2 * k);
      == x * exp(x, 2 * k - 1);
      == x * (x * exp(x, 2 * k - 2));
      == x * x * exp(x, 2 * (k - 1));
      == { exp_double_lemma(x, k - 1); }
      (x * x) * exp(x * x, k - 1);
      == exp(x * x, k);
    }
  }
}