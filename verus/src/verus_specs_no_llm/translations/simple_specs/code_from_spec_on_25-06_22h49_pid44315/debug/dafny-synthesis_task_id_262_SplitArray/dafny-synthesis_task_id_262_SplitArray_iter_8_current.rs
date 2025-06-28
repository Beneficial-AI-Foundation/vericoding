use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn SplitArray(arr: Vec<i32>, L: usize) -> (firstPart: Seq<i32>, secondPart: Seq<i32>)
    requires
        L <= arr.len()
    ensures
        firstPart.len() == L,
        secondPart.len() == arr.len() - L,
        firstPart + secondPart == arr@
{
    let firstPart: Seq<i32> = arr@.subrange(0, L as int);
    let secondPart: Seq<i32> = arr@.subrange(L as int, arr.len() as int);
    
    // Proof assertions to help Verus verify the postconditions
    assert(firstPart.len() == L as int);
    assert(secondPart.len() == (arr.len() - L) as int);
    
    // Prove the concatenation property
    assert(arr@.subrange(0, L as int) + arr@.subrange(L as int, arr.len() as int) == arr@);
    
    (firstPart, secondPart)
}

}