// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn maxcheck(s: Vec<nat>, i: int, max: int) -> int
    requires
        0 <= i <= s.len()
reads s
{
    0
}

spec fn spec_max(s: Vec<nat>) -> a:int
    requires
        s.len() > 0
    ensures
        forall |x: int| 0 <= x < s.len() ==> a >= s.index(x),
        a in s.index(..)
;

proof fn lemma_max(s: Vec<nat>) -> (a: int)
    requires
        s.len() > 0
    ensures
        forall |x: int| 0 <= x < s.len() ==> a >= s.index(x),
        a in s.index(..)
{
    0
}

}