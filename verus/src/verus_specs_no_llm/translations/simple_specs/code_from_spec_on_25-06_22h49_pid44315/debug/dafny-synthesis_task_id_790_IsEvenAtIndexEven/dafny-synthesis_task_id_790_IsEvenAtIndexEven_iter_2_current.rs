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
            // We found a counterexample: index is even but lst[index] is not even
            // This means the property doesn't hold for all elements
            assert(!IsEven(lst.spec_index(index)));
            assert(IsEven(index));
            assert(index < lst.len());
            return false;
        }
        index = index + 1;
    }
    
    // At this point, we've checked all indices from 0 to lst.len()-1
    // The loop invariant tells us that for all i in [0, index), the property holds
    // Since index == lst.len(), this means the property holds for all valid indices
    assert(index == lst.len());
    assert(forall i :: 0 <= i < lst.len() ==> (IsEven(i) ==> IsEven(lst.spec_index(i))));
    return true;
}

}