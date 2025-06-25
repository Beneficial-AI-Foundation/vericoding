// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

spec fn stepEndsAt(xs: Seq<Steps>, n: nat) -> bool {
    stepSum(xs) == n
}
spec fn allEndAtN(ss: set<seq<Steps> >, n: nat) -> bool {
    forall|xs: int|  xs in ss ==> stepEndsAt(xs, n)
}

fn climbStairs(n: nat) -> (count: nat)
    ensures exists ss: set< seq<Steps> > :: count == ss.len() and allEndAtN(ss, n)
{
}

}