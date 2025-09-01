function Prime(p: nat) : bool
{
    p > 1 &&
    forall k :: 1 < k < p ==> p % k != 0
}

// <vc-helpers>
// No changes needed in helpers
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
ans := false;
  var a := 2;
  while a * a * a <= x {
    if Prime(a) && x % a == 0 {
      var x1 := x / a;
      var b := 2;
      while b * b <= x1 {
        if Prime(b) && x1 % b == 0 {
          var c := x1 / b;
          if Prime(c) && x == a * b * c {
            ans := true;
            return;
          }
        }
        b := b + 1;
      }
    }
    a := a + 1;
  }
// </vc-code>

