function Prime(p: nat) : bool
{
    p > 1 &&
    forall k :: 1 < k < p ==> p % k != 0
}

// <vc-helpers>
function IsPrime(p: nat) : bool
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
    invariant 2 <= a <= x + 1
    invariant ans == (exists a_prime: nat, b_prime: nat, c_prime: nat ::
                       IsPrime(a_prime) && IsPrime(b_prime) && IsPrime(c_prime) && a_prime < a
                       && a_prime * b_prime * c_prime == x)
                   // The loop invariant needs to state that if such primes exist with a_prime < a, then `ans` is true.
                   // More simply, we encode that if ans is found, we immediately return.
                   // Thus, if we reach this loop invariant and ans is true, then we have already returned.
                   // If ans is false, then no such triple exists with a_prime < a.
  {
    if IsPrime(a) {
      if x % a == 0 {
        var remaining1 := x / a;
        if remaining1 >= a { // remaining1 can't be 1 if a*a*a <= x and a is prime
          var b: nat := a;
          while b * b <= remaining1
            invariant a <= b <= remaining1 + 1
            invariant ans == (exists b_prime: nat, c_prime: nat ::
                               IsPrime(a) && IsPrime(b_prime) && IsPrime(c_prime) && a*b_prime*c_prime == x
                               && a <= b_prime < b)
          {
            if IsPrime(b) {
              if remaining1 % b == 0 {
                var c := remaining1 / b;
                if b <= c && IsPrime(c) {
                  ans := true;
                  return;
                }
              }
            }
            b := b + 1;
          }
        }
      }
    }
    a := a + 1;
  }
}
// </vc-code>

