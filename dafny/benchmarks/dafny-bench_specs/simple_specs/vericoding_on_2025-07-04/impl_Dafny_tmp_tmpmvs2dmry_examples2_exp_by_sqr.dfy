//ATOM

function exp(x: real, n: nat) :real
{
  if(n == 0) then 1.0
  else if (x==0.0) then 0.0
  else if (n ==0 && x == 0.0) then 1.0
  else x*exp(x, n-1)
}

/* code modified by LLM (iteration 4): Fixed exponentiation multiplication property with proper induction */
lemma exp_multiply_property(x: real, a: nat, b: nat)
  ensures exp(x, a) * exp(x, b) == exp(x, a + b)
{
  if a == 0 {
    // Base case: exp(x, 0) * exp(x, b) == 1.0 * exp(x, b) == exp(x, b) == exp(x, 0 + b)
  } else if x == 0.0 {
    // When x == 0.0, exp(x, a) == 0.0 for a > 0, and exp(x, a + b) == 0.0 for a + b > 0
  } else {
    // Inductive case: exp(x, a) == x * exp(x, a-1)
    exp_multiply_property(x, a - 1, b);
    assert exp(x, a - 1) * exp(x, b) == exp(x, (a - 1) + b);
    assert exp(x, a) * exp(x, b) == x * exp(x, a - 1) * exp(x, b);
    assert x * exp(x, a - 1) * exp(x, b) == x * exp(x, (a - 1) + b);
    assert x * exp(x, (a - 1) + b) == exp(x, a + b);
  }
}

/* code modified by LLM (iteration 4): Fixed power rule lemma with correct base and inductive cases */
lemma exp_power_rule(x: real, m: nat)
  ensures exp(x, 2 * m) == exp(x * x, m)
{
  if m == 0 {
    // Base case: exp(x, 0) == 1.0 == exp(x * x, 0)
  } else if x == 0.0 {
    // When x == 0.0: exp(0.0, 2 * m) == 0.0 and exp(0.0, m) == 0.0 for m > 0
  } else {
    // Inductive case
    exp_power_rule(x, m - 1);
    exp_multiply_property(x, 2, 2 * (m - 1));
    assert exp(x, 2 * m) == exp(x, 2) * exp(x, 2 * (m - 1));
    assert exp(x, 2) == x * x;
    assert exp(x, 2 * (m - 1)) == exp(x * x, m - 1);
    assert exp(x, 2 * m) == (x * x) * exp(x * x, m - 1);
    assert (x * x) * exp(x * x, m - 1) == exp(x * x, m);
  }
}

/* code modified by LLM (iteration 4): Simplified square property lemma */
lemma exp_square_property(x: real, n: nat)
  requires n % 2 == 0
  ensures exp(x * x, n / 2) == exp(x, n)
{
  var m := n / 2;
  assert n == 2 * m;
  exp_power_rule(x, m);
}

//IMPL 

method exp_by_sqr(x0: real, n0: nat) returns (r:real)
requires x0 >= 0.0
ensures r == exp(x0, n0)
{
  if n0 == 0 {
    r := 1.0;
  } else {
    var x := x0;
    var n := n0;
    r := 1.0;
    
    while n > 0
      invariant r * exp(x, n) == exp(x0, n0)
      invariant x >= 0.0
      decreases n
    {
      if n % 2 == 1 {
        /* code modified by LLM (iteration 4): Fixed odd case with proper multiplication property */
        assert exp(x, n) == x * exp(x, n - 1);
        assert r * exp(x, n) == r * x * exp(x, n - 1);
        assert r * x * exp(x, n - 1) == (r * x) * exp(x, n - 1);
        r := r * x;
        n := n - 1;
        assert r * exp(x, n) == exp(x0, n0);
      } else {
        /* code modified by LLM (iteration 4): Fixed even case with square property */
        assert n % 2 == 0 && n > 0;
        exp_square_property(x, n);
        assert exp(x * x, n / 2) == exp(x, n);
        assert r * exp(x, n) == r * exp(x * x, n / 2);
        x := x * x;
        n := n / 2;
        assert r * exp(x, n) == exp(x0, n0);
      }
    }
  }
}