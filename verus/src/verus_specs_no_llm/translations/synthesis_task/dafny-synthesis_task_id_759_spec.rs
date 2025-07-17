// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_IsDecimalWithTwoPrecision(s: String) -> result: bool
    ensures
        result ==> (exists |i: int| 0 <= i < s.len() && s.index(i) == '.' && s.len() - i - 1 == 2),
        !result ==> !(exists |i: int| 0 <= i < s.len() && s.index(i) == '.' && s.len() - i - 1 == 2)
;

proof fn lemma_IsDecimalWithTwoPrecision(s: String) -> (result: bool)
    ensures
        result ==> (exists |i: int| 0 <= i < s.len() && s.index(i) == '.' && s.len() - i - 1 == 2),
        !result ==> !(exists |i: int| 0 <= i < s.len() && s.index(i) == '.' && s.len() - i - 1 == 2)
{
    false
}

}