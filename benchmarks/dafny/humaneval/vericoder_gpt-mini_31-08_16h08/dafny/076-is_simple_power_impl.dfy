function power(x: nat, y: nat): nat {
    if y == 0 then 1 else x * power(x, y-1)
}

// <vc-helpers>
lemma {:induction b} power_mul(x: nat, a: nat, b: nat)
  decreases b
  ensures power(x, a + b) == power(x, a) * power(x, b)
{
  if b == 0 {
    // power(x, a + 0) == power(x, a) and power(x,0) == 1
  } else {
    power_mul(x, a, b - 1);
    // power(x, a + b) == x * power(x, a + b - 1)
    assert power(x, a + b) == x * power(x, a + b - 1);
    // by IH: power(x, a + b - 1) == power(x, a) * power(x, b - 1)
    assert power(x, a + b - 1) == power(x, a) * power(x, b - 1);
    // and power(x, b) == x * power(x, b - 1)
    assert power(x, b) == x * power(x, b - 1);
    // combine equalities
    assert power(x, a + b) == x * (power(x, a) * power(x, b - 1));
    assert x * (power(x, a) * power(x, b - 1)) == power(x, a) * (x * power(x, b - 1));
    assert power(x, a) * (x * power(x, b - 1)) == power(x, a) * power(x, b);
  }
}
// </vc-helpers>

// <vc-spec>
method is_simple_power(x: nat, n: int) returns (ans : bool)
    // pre-conditions-start
    requires x > 0
    // pre-conditions-end
    // post-conditions-start
    ensures ans <==> exists y :: n == power(x, y)
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
  if n < 1 {
    ans := false;
    return;
  }
  if x == 1 {
    // power(1, y) == 1 for all y, so only n == 1 can satisfy
    ans := (n == 1);
    return;
  }
  var n_nat := n as nat;
  var m: nat := n_nat;
  var k: nat := 0;
  // Loop removes all factors x from m, maintaining n_nat == m * power(x, k)
  while m % x == 0
    invariant n_nat == m * power(x, k)
    invariant m > 0
    decreases m
  {
    var oldm := m;
    var oldk := k;
    // update: divide out one factor of x
    m := oldm / x;
    k := oldk + 1;
    // oldm == m * x because oldm % x == 0
    assert oldm == m * x;
    // from invariant before update: n_nat == oldm * power(x, oldk)
    assert n_nat == oldm * power(x, oldk);
    // power(x, oldk + 1) == x * power(x, oldk)
    assert power(x, oldk + 1) == x * power(x, oldk);
    // combine to re-establish invariant: n_nat == m * power(x, k)
    assert n_nat == m * power(x, k);
  }
  // After loop, m is not divisible by x. If m == 1 then n_nat == power(x, k).
  ans := (m == 1);
}
// </vc-code>

