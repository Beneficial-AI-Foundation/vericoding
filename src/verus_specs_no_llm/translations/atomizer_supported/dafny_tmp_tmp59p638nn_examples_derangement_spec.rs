// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

spec fn derangement(s: Seq<nat>) -> bool {
    forall|i: int| 0 <= i < s.len() ==> s[i] != i
}

spec fn permutation(s: Seq<nat>) -> bool {
    forall|i: int| 0 <= i < s.len() ==> i in s
}

}