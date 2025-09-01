function Prime(p: nat) : bool
{
    p > 1 &&
    forall k :: 1 < k < p ==> p % k != 0
}

// <vc-helpers>
// No helpers required for this proof.
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
    invariant a >= 2
    invariant forall a0 :: 2 <= a0 < a ==>
                forall b0, c0 :: 2 <= b0 <= x / a0 && 2 <= c0 && Prime(a0) && Prime(b0) && Prime(c0) ==> x != a0 * b0 * c0
  {
    var b := 2;
    while b <= x / a
      decreases (x / a) - b
      invariant 2 <= a && a <= x + 1
      invariant forall b0 :: 2 <= b0 < b ==>
                  forall c0 :: 2 <= c0 && Prime(a) && Prime(b0) && Prime(c0) ==> x != a * b0 * c0
    {
      if a <= x && b <= x / a {
        if x % (a * b) == 0 {
          var c := x / (a * b);
          if 2 <= c && Prime(a) && Prime(b) && Prime(c) {
            ans := true;
            return;
          }
        }
      }
      b := b + 1;
    }
    // After inner loop, no triple with this 'a'
    assert forall b0, c0 :: 2 <= b0 <= x / a && 2 <= c0 && Prime(a) && Prime(b0) && Prime(c0) ==> x != a * b0 * c0;
    a := a + 1;
  }
  // No triple found for any 'a' in 2..x
  assert forall a0, b0, c0 :: 2 <= a0 <= x && 2 <= b0 && 2 <= c0 && Prime(a0) && Prime(b0) && Prime(c0) ==> x != a0 * b0 * c0;
  ans := false;
  return;
}
// </vc-code>

