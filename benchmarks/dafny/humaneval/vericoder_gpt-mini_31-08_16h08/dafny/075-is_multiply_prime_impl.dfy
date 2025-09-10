function Prime(p: nat) : bool
{
    p > 1 &&
    forall k :: 1 < k < p ==> p % k != 0
}

// <vc-helpers>
lemma DivBound(x: nat, a: nat)
  requires a > 0
  ensures x < a * (x / a + 1)
{
  var q := x / a;
  // By division properties: x = a*q + r with 0 <= r < a
  assert x - a * q < a;
  assert x < a * q + a;
  assert a * q + a == a * (q + 1);
}

lemma MulWithCgt(x: nat, a: nat, b0: nat, c0: nat)
  requires a > 0
  requires b0 >= x / a + 1
  requires c0 >= 2
  ensures a * b0 * c0 > x
{
  // From DivBound we get x < a*(x/a + 1) and b0 >= x/a + 1 implies a*b0 >= a*(x/a + 1)
  assert x < a * (x / a + 1);
  assert a * b0 >= a * (x / a + 1);
  assert a * b0 > x;
  assert a * b0 * c0 > x;
}
// </vc-helpers>

// <vc-spec>
method is_multiply_prime(x: nat) returns (ans : bool)
    // pre-conditions-start
    requires x > 1
    // pre-conditions-end
    // post-conditions-start
    ensures ans <==> exists a: nat, b: nat, c: nat :: Prime(a) && Prime(b) && Prime(c) && x == a * b * c
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
  var a := 2;
  while a <= x
    decreases x - a
    invariant 2 <= a <= x + 1
    invariant forall a0 :: 2 <= a0 < a && Prime(a0) ==>
                 forall b0, c0 :: 2 <= b0 && 2 <= c0 && Prime(b0) && Prime(c0) ==> x != a0 * b0 * c0
  {
    var b := 2;
    while b <= x / a
      decreases (x / a) - b
      invariant 2 <= b <= x / a + 1
      invariant 2 <= a && a <= x + 1
      invariant Prime(a) ==> forall b0 :: 2 <= b0 < b && Prime(b0) ==>
                   forall c0 :: 2 <= c0 && Prime(c0) ==> x != a * b0 * c0
    {
      if x % (a * b) == 0 {
        var c := x / (a * b);
        if 2 <= c && Prime(a) && Prime(b) && Prime(c) {
          ans := true;
          return;
        }
      }
      b := b + 1;
    }
    // From loop exit: b == x / a + 1
    assert b == x / a + 1;
    // For b0 <= x / a we have checked there is no c with a * b0 * c == x (when Prime(a))
    if Prime(a) {
      assert forall b0, c0 :: 2 <= b0 <= x / a && 2 <= c0 && Prime(b0) && Prime(c0) ==> x != a * b0 * c0;
      // For b0 > x / a, we use MulWithCgt to show a * b0 * c0 > x, hence cannot be equal to x
      assert forall b0, c0 :: x / a + 1 <= b0 <= x && 2 <= c0 && Prime(b0) && Prime(c0) ==> a * b0 * c0 > x by {
        var bb := b0;
        var cc := c0;
        reveal MulWithCgt(x, a, bb, cc);
        assert a * bb * cc > x;
      };
      // Combine the two ranges to conclude no representation for this a
      assert forall b0, c0 :: 2 <= b0 <= x && 2 <= c0 && Prime(b0) && Prime(c0) ==> x != a * b0 * c0;
    }
    a := a + 1;
  }
  // From outer loop exit: a == x + 1
  assert a == x + 1;
  // By the outer invariant, for all prime a0 in [2..x] there is no representation
  assert forall a0, b0, c0 :: 2 <= a0 <= x && 2 <= b0 <= x && 2 <= c0 <= x && Prime(a0) && Prime(b0) && Prime(c0) ==> x != a0 * b0 * c0;
  ans := false;
  return;
}
// </vc-code>

