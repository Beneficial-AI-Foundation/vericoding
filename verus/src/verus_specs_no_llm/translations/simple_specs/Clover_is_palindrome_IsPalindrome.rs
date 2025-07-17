// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_IsPalindrome(x: Seq<char>) -> result: bool
    ensures
        result <==> (forall |i: int| 0 <= i < x.len() ==> x.index(i) == x.index(x.len() - i - 1))
;

proof fn lemma_IsPalindrome(x: Seq<char>) -> (result: bool)
    ensures
        result <==> (forall |i: int| 0 <= i < x.len() ==> x.index(i) == x.index(x.len() - i - 1))
{
    false
}

}