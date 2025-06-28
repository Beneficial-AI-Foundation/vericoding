// Translated from Dafny
use builtin::*;
use builtin_macros::*;

use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn IsEven(n: int) -> bool {
    n % 2 == 0
}

fn IsEvenAtIndexEven(lst: Seq<int>) -> (result: bool)
    ensures
        result <==> forall i :: 0 <= i < lst.len() ==> (IsEven(i) ==> IsEven(lst.spec_index(i)))
{
    return false;
}

}