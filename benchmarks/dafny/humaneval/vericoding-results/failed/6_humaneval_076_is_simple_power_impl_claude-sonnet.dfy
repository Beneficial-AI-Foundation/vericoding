// <vc-preamble>
function power(x: nat, y: nat): nat {
    if y == 0 then 1 else x * power(x, y-1)
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): comprehensive lemmas for power properties and existence proofs */
lemma PowerBaseCase(x: nat)
  requires x > 0
  ensures power(x, 0) == 1
{
}

lemma PowerOneExists(x: nat)
  requires x > 0
  ensures exists y :: 1 == power(x, y)
{
  assert power(x, 0) == 1;
}

lemma PowerUniqueness(x: nat, y1: nat, y2: nat)
  requires x > 1
  requires power(x, y1) == power(x, y2)
  ensures y1 == y2
{
  if y1 != y2 {
    if y1 < y2 {
      PowerGrowthLemma(x, y1, y2);
      assert power(x, y1) < power(x, y2);
      assert false;
    } else {
      PowerGrowthLemma(x, y2, y1);
      assert power(x, y2) < power(x, y1);
      assert false;
    }
  }
}

lemma PowerGrowthLemma(x: nat, y1: nat, y2: nat)
  requires x > 1
  requires y1 < y2
  ensures power(x, y1) < power(x, y2)
{
  if y2 == y1 + 1 {
    assert power(x, y2) == x * power(x, y1);
    assert x > 1;
  } else {
    PowerGrowthLemma(x, y1, y2 - 1);
    assert power(x, y2) == x * power(x, y2 - 1);
  }
}

lemma PowerOverflow(x: nat, n: int)
  requires x > 1
  requires n > 0
  ensures exists bound :: forall y :: y > bound ==> power(x, y) > n
{
  var bound := n;
  assert forall y :: y > bound ==> power(x, y) > n;
}
// </vc-helpers>

// <vc-spec>
method is_simple_power(x: nat, n: int) returns (ans : bool)

    requires x > 0

    ensures ans <==> exists y :: n == power(x, y)
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 5): handle all cases with proper witnesses and bounds */
  if n == 1 {
    ans := true;
    PowerBaseCase(x);
    assert power(x, 0) == 1;
    return;
  }
  
  if n <= 0 {
    ans := false;
    return;
  }
  
  if x == 1 {
    ans := (n == 1);
    if n == 1 {
      PowerBaseCase(x);
      assert power(x, 0) == 1;
    }
    return;
  }
  
  var current := 1;
  var y := 0;
  
  while current < n && current <= n / x
    invariant current == power(x, y)
    invariant current >= 1
    invariant x > 0
    invariant y >= 0
    decreases n - current
  {
    current := current * x;
    y := y + 1;
  }
  
  ans := (current == n);
  
  if ans {
    assert n == power(x, y);
  } else {
    if x > 1 {
      PowerGrowthLemma(x, 0, y + 1);
      if current > n {
        if y > 0 {
          assert power(x, y - 1) < n < power(x, y);
          PowerUniqueness(x, y - 1, y);
        }
      }
    }
  }
}
// </vc-code>
