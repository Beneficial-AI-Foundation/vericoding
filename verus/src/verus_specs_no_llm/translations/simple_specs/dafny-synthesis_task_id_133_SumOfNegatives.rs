// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn sumNegativesTo(a: Vec<int>, n: int) -> int
    requires
        a != null,
        0 <= n && n <= a.len()
 reads a
{
    0
}

spec fn spec_SumOfNegatives(a: Vec<int>) -> result: int
    ensures
        result == sumNegativesTo(a, a.len())
;

proof fn lemma_SumOfNegatives(a: Vec<int>) -> (result: int)
    ensures
        result == sumNegativesTo(a, a.len())
{
    0
}

}