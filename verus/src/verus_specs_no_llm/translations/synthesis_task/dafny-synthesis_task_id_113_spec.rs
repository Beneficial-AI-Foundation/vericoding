// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn IsDigit(c: char) -> bool {
    48 <= c as int <= 57
}

spec fn spec_IsInteger(s: String) -> result: bool
    ensures
        result <==> (s.len() > 0) && (forall |i: int| 0 <= i < s.len() ==> IsDigit(s.index(i)))
;

proof fn lemma_IsInteger(s: String) -> (result: bool)
    ensures
        result <==> (s.len() > 0) && (forall |i: int| 0 <= i < s.len() ==> IsDigit(s.index(i)))
{
    false
}

}