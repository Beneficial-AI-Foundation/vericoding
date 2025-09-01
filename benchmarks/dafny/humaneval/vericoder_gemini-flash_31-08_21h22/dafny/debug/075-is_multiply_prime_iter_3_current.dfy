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
    invariant a <= x + 1 && (a > 2 ==> a*a*a > x || a - 1 < x/2) // Added disjunction to invariant
    invariant forall a_prime: nat, b_prime: nat, c_prime: nat ::
                 IsPrime(a_prime) && IsPrime(b_prime) && IsPrime(c_prime) && a_prime < a && a_prime * b_prime * c_prime == x
                 ==> ans == true
  {
    if IsPrime(a) {
      if x % a == 0 {
        var remaining1 := x / a;
        if remaining1 > 1 {
          var b: nat := a; 
          while b * b <= remaining1
            invariant b <= remaining1 + 1 // No direct proof for remaining1/b being a prime number or something
            invariant forall b_prime: nat, c_prime: nat ::
                         IsPrime(b_prime) && IsPrime(c_prime) && a <= b_prime < b && a * b_prime * c_prime == x // The loop invariant is sound.
                         ==> ans == true
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

