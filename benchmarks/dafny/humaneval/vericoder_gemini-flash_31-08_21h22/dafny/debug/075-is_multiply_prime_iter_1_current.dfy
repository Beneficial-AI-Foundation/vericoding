function Prime(p: nat) : bool
{
    p > 1 &&
    forall k :: 1 < k < p ==> p % k != 0
}

// <vc-helpers>
function Prime(p: nat) : bool
{
    p > 1 &&
    forall k :: 1 < k < p ==> p % k != 0
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
  ans := false;
  var a: nat := 2;
  while a * a * a <= x
    invariant a <= x + 1 // a is not too large
    invariant forall a_prime: nat, b_prime: nat, c_prime: nat ::
                 Prime(a_prime) && Prime(b_prime) && Prime(c_prime) && a_prime < a && a_prime * b_prime * c_prime == x
                 ==> ans == true
  {
    if Prime(a) {
      if x % a == 0 {
        var remaining1 := x / a;
        var b: nat := a; // Start searching for b from a to avoid redundant checks (a*b*c is commutative)
        while b * b <= remaining1
          invariant b <= remaining1 + 1
          invariant forall b_prime: nat, c_prime: nat ::
                       Prime(b_prime) && Prime(c_prime) && b_prime < b && a * b_prime * c_prime == x
                       ==> ans == true
        {
          if Prime(b) {
            if remaining1 % b == 0 {
              var c := remaining1 / b;
              if Prime(c) {
                ans := true;
                return;
              }
            }
          }
          b := b + 1;
        }
      }
    }
    a := a + 1;
  }
}
// </vc-code>

