// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

spec fn IsEven(n: int) -> bool {
    n % 2 == 0
}

fn IsEvenAtIndexEven(lst: Seq<int>) -> (result: bool)
    ensures result <==> forall|i: int| 0 <= i < lst.len() ==> (IsEven(i) ==> IsEven(lst[i]))
{
}

}