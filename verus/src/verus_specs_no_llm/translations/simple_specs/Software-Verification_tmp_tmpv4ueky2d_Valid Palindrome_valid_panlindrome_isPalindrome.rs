// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_isPalindrome(s: Vec<char>) -> result: bool
    requires
        1<= s.len() <= 200000
    ensures
        result <==> (forall |i: int| 0 <= i < s.len() / 2 ==> s.index(i) == s.index(s.len() - 1 - i))
;

proof fn lemma_isPalindrome(s: Vec<char>) -> (result: bool)
    requires
        1<= s.len() <= 200000
    ensures
        result <==> (forall |i: int| 0 <= i < s.len() / 2 ==> s.index(i) == s.index(s.len() - 1 - i))
{
    false
}

}