// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_allDigits(s: String) -> result: bool
    ensures
        result <==> (forall |i: int| 0 <= i < s.len() ==> s.index(i) in "0123456789")
;

proof fn lemma_allDigits(s: String) -> (result: bool)
    ensures
        result <==> (forall |i: int| 0 <= i < s.len() ==> s.index(i) in "0123456789")
{
    false
}

}