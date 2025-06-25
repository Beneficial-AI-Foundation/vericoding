// Translated from Dafny
use builtin::*;
use builtin_macros::*;

use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn stepEndsAt(xs: Seq<Steps>, n: nat) -> bool {
    stepSum(xs) == n
}
spec fn allEndAtN(ss: set<seq<Steps> >, n: nat) -> bool {
    forall xs ::  xs in ss ==> stepEndsAt(xs, n)
}

fn climbStairs(n: nat) -> (count: nat)
    ensures
        exists ss: set< seq<Steps> > :: count == ss.len() && allEndAtN(ss, n)
{
    return 0;
}

}