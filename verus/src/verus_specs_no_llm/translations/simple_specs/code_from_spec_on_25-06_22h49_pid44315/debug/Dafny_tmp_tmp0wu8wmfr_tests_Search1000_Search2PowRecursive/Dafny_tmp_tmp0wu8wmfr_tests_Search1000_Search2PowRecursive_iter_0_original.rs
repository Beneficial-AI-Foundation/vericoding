// Translated from Dafny
use builtin::*;
use builtin_macros::*;

use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn Is2Pow(n: int) -> bool {
    if n < 1 then
    false
  else if n == 1 then
    true
  else
    n%2 == 0 && Is2Pow(n/2)
}

fn Search2PowRecursive(a: Vec<int>, i: int, n: int, x: int) -> (k: int)
    requires
        0 <= i <= i+n <= a.len(),
        forall p,q | i <= p < q < i+n :: a.spec_index(p) <= a.spec_index(q),
        Is2Pow(n+1)
    ensures
        i <= k <= i+n,
        forall r | i <= r < k :: a.spec_index(r) < x,
        forall r | k <= r < i+n :: a.spec_index(r) >= x
{
    return 0;
}

}