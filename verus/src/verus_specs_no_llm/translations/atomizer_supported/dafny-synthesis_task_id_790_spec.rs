// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn IsEven(n: int) -> bool {
    n % 2 == 0
}

spec fn spec_IsEvenAtIndexEven(lst: Seq<int>) -> result: bool
    ensures
        result <==> forall |i: int| 0 <= i < lst.len() ==> (IsEven(i) ==> IsEven(lst.index(i)))
;

proof fn lemma_IsEvenAtIndexEven(lst: Seq<int>) -> (result: bool)
    ensures
        result <==> forall |i: int| 0 <= i < lst.len() ==> (IsEven(i) ==> IsEven(lst.index(i)))
{
    false
}

}