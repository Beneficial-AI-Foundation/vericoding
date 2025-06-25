// Translated from Dafny
use builtin::*;
use builtin_macros::*;

use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn IsPrime(n: int) -> bool {
    2 <= n && forall m :: 2 <= m < n ==> n % m != 0 // WISH It would be great to think about the status of modulo as a trigger
}
spec fn AllPrimes(s: set<int>, bound: int) -> bool {
    // s contains only primes
  (forall x :: x in s ==> IsPrime(x)) &&
  // every prime up to "bound" is included in s
  (forall p :: IsPrime(p) && p <= bound ==> p in s)
}
spec fn IsPrime_Alt(n: int) -> bool {
    2 <= n && forall m :: 2 <= m < n && IsPrime(m) ==> n % m != 0
}

}