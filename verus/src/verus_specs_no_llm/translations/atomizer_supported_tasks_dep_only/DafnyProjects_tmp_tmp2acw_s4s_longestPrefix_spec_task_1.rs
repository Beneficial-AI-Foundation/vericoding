// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_longestPrefix(a: Vec<int>, b: array <int>) -> i: nat
    ensures
        i <= a.len() && i <= b.len(),
        a.index(..i) == b.index(..i),
        i < a.len() && i < b.len() ==> a.index(i) != b.index(i)
;

proof fn lemma_longestPrefix(a: Vec<int>, b: array <int>) -> (i: nat)
    ensures
        i <= a.len() && i <= b.len(),
        a.index(..i) == b.index(..i),
        i < a.len() && i < b.len() ==> a.index(i) != b.index(i)
{
    0
}

}