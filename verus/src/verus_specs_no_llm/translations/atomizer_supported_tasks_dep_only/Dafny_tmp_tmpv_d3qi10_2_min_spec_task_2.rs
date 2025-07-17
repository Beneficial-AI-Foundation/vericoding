// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_minArray(a: Vec<int>) -> m: int
    requires
        a!= null  && a.len() > 0
    ensures
        forall k | 0 <= k < a.len() :: m <= a.index(k),
        exists k | 0 <= k < a.len() :: m == a.index(k)
;

proof fn lemma_minArray(a: Vec<int>) -> (m: int)
    requires
        a!= null  && a.len() > 0
    ensures
        forall k | 0 <= k < a.len() :: m <= a.index(k),
        exists k | 0 <= k < a.len() :: m == a.index(k)
{
    0
}

}