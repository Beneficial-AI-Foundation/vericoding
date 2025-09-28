// <vc-preamble>
function power(x: nat, y: nat): nat {
    if y == 0 then 1 else x * power(x, y-1)
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): power_positive shows power(x,y) >= 1 when x>0 */
lemma power_positive(x: nat, y: nat)
  requires x > 0
  ensures power(x,y) >= 1
{
  if y == 0 {
    assert power(x,0) == 1;
  } else {
    power_positive(x, y-1);
    assert power(x,y) == x * power(x, y-1);
    assert power(x,y) >= 1;
  }
}

/* helper modified by LLM (iteration 5): power_succ relates power(x,y+1) to x * power(x,y) */
lemma power_succ(x: nat, y: nat)
  ensures power(x, y+1) == x * power(x, y)
{
  if y == 0 {
    assert power(x,1) == x * power(x,0);
  } else {
    power_succ(x, y-1);
    assert power(x, y+1) == x * power(x, y);
  }
}

/* helper modified by LLM (iteration 5): power_one shows power(1,y) == 1 for all y */
lemma power_one(y: nat)
  ensures power(1, y) == 1
{
  if y == 0 {
    assert power(1,0) == 1;
  } else {
    power_one(y-1);
    assert power(1,y) == 1;
  }
}

// </vc-helpers>

// <vc-spec>
method is_simple_power(x: nat, n: int) returns (ans : bool)

    requires x > 0

    ensures ans <==> exists y :: n == power(x, y)
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 5): simplified handling of n<0 and x==1; iterate powers using nat N */
  if n < 0 {
    ans := false;
    return;
  }
  var N: nat := n;
  if x == 1 {
    ans := (N == 1);
    return;
  }
  var p: nat := 1;
  var y: nat := 0;
  while p < N
    invariant p == power(x, y)
    invariant y >= 0
    decreases N - p
  {
    var newp := p * x;
    var newy := y + 1;
    power_succ(x, y);
    assert power(x,newy) == x * power(x,y);
    assert newp == power(x,newy);
    p := newp;
    y := newy;
  }
  ans := (p == N);
}
// </vc-code>
