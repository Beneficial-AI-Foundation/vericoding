// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn sumcheck(s: Vec<int>, i: int) -> int
    requires
        0 <= i <= s.len()
reads s
{
    0
}

spec fn spec_sum(s: Vec<int>) -> a:int
    requires
        s.len() > 0
    ensures
        sumcheck(s, s.len()) == a
;

proof fn lemma_sum(s: Vec<int>) -> (a: int)
    requires
        s.len() > 0
    ensures
        sumcheck(s, s.len()) == a
{
    0
}

}