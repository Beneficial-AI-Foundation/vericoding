// Translated from Dafny
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
    let mut index = 0;
    
    while index < lst.len()
        invariant
            0 <= index <= lst.len(),
            forall i :: 0 <= i < index ==> (IsEven(i) ==> IsEven(lst.spec_index(i)))
    {
        if IsEven(index) && !IsEven(lst.spec_index(index)) {
            return false;
        }
        index = index + 1;
    }
    
    return true;
}

}