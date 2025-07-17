// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_ContainsK(s: Seq<int>, k: int) -> result: bool
    ensures
        result <==> k in s
;

proof fn lemma_ContainsK(s: Seq<int>, k: int) -> (result: bool)
    ensures
        result <==> k in s
{
    false
}

}