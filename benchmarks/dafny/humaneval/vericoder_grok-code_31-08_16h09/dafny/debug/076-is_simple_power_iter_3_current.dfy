function power(x: nat, y: nat): nat {
    if y == 0 then 1 else x * power(x, y-1)
}

// <vc-helpers>
function power(x: nat, y: nat): nat {
    if y == 0 then 1 else x * power(x, y-1)
}

lemma NoPowerForNonPositive(n: int, x: nat)
requires x > 0
requires n <= 0
ensures forall y:nat :: n != power(x, y)
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
  if n <= 0 {
    NoPowerForNonPositive(n, x);
    assert forall y :: nat :: n != power(x, y);
    return false;
  }
  if x == 1 {
    return n == 1;
  }
  var acc := 1;
  var y := 0;
  while acc != n && acc < n
    invariant 0 < x
    invariant y == 0 ==> acc == 1
    invariant acc == power(x, y)
    invariant y >= 0
    invariant x > 1
    decreases n - acc
  {
    acc := acc * x;
    y := y + 1;
  }
  return acc == n;
}
// </vc-code>

