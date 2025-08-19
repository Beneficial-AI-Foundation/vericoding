//ATOM

function exp(x: real, n: nat) :real
{
  if(n == 0) then 1.0
  else if (x==0.0) then 0.0
  else if (n ==0 && x == 0.0) then 1.0
  else x*exp(x, n-1)
}

/* code modified by LLM (iteration 3): simplified lemma to avoid prover complexity */
lemma exp_square_property(x: real, n: nat)
  requires n % 2 == 0
  ensures exp(x, n) == exp(x * x, n / 2)
  decreases n
{
  if n == 0 {
    // Base case: both sides equal 1.0
  } else if n == 2 {
    // Simple case: exp(x, 2) = x * x = exp(x*x, 1)
    calc {
      exp(x, 2);
      == x * exp(x, 1);
      == x * x * exp(x, 0);
      == x * x * 1.0;
      == x * x;
      == (x * x) * 1.0;
      == (x * x) * exp(x * x, 0);
      == exp(x * x, 1);
    }
  } else {
    // For larger even n, use recursive structure
    exp_square_property(x, n - 2);
  }
}

/* code modified by LLM (iteration 3): removed problematic lemma that was causing internal error */

//IMPL 

method exp_by_sqr(x0: real, n0: nat) returns (r:real)
requires x0 >= 0.0
ensures r == exp(x0, n0)
{
    var x := x0;
    var n := n0;
    var result := 1.0;
    
    while n > 0
        invariant result * exp(x, n) == exp(x0, n0)
        decreases n
    {
        if n % 2 == 1 {
            /* code modified by LLM (iteration 3): simplified assertion for odd case */
            result := result * x;
            n := n - 1;
        } else {
            /* code modified by LLM (iteration 3): use simplified approach for even case */
            assert n % 2 == 0;
            if n > 0 {
                exp_square_property(x, n);
            }
            x := x * x;
            n := n / 2;
        }
    }
    
    r := result;
}