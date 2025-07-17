// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_IsLengthOdd(s: String) -> result: bool
    ensures
        result <==> s.len() % 2 == 1
;

proof fn lemma_IsLengthOdd(s: String) -> (result: bool)
    ensures
        result <==> s.len() % 2 == 1
{
    false
}

}