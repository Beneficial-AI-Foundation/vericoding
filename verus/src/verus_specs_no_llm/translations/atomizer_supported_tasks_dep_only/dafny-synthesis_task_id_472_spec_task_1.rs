// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_ContainsConsecutiveNumbers(a: Vec<int>) -> result: bool
    requires
        a.len()>0
    ensures
        result <==> (exists |i: int| 0 <= i < a.len() - 1 && a.index(i) + 1 == a.index(i + 1))
;

proof fn lemma_ContainsConsecutiveNumbers(a: Vec<int>) -> (result: bool)
    requires
        a.len()>0
    ensures
        result <==> (exists |i: int| 0 <= i < a.len() - 1 && a.index(i) + 1 == a.index(i + 1))
{
    false
}

}