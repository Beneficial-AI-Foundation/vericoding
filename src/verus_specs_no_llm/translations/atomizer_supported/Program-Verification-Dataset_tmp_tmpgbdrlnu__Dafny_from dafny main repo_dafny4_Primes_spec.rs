// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

spec fn IsPrime(n: int) -> bool {
    2 <= n and forall|m: int| 2 <= m < n ==> n % m != 0 // WISH It would be great to think about the status of modulo as a trigger
}

spec fn AllPrimes(s: set<int>, bound: int) -> bool {
    // s contains only primes
  (forall|x: int| x in s ==> IsPrime(x)) and
  // every prime up to "bound" is included in s
  (forall|p: int| IsPrime(p) and p <= bound ==> p in s)
}

spec fn IsPrime_Alt(n: int) -> bool {
    2 <= n and forall|m: int| 2 <= m < n and IsPrime(m) ==> n % m != 0
}

}