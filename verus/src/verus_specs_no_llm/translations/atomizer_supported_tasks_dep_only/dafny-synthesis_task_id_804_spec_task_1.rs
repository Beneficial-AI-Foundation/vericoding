// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn IsEven(n: int) -> bool {
    n % 2 == 0
}

spec fn spec_IsProductEven(a: Vec<int>) -> result: bool
    ensures
        result <==> exists |i: int| 0 <= i < a.len() && IsEven(a.index(i))
;

proof fn lemma_IsProductEven(a: Vec<int>) -> (result: bool)
    ensures
        result <==> exists |i: int| 0 <= i < a.len() && IsEven(a.index(i))
{
    false
}

}