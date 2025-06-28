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
    let firstPart = arr@.subrange(0, L as int);
    let secondPart = arr@.subrange(L as int, arr.len() as int);
    
    // Proof that the postconditions hold
    assert(firstPart.len() == L);
    assert(secondPart.len() == arr.len() - L);
    
    // Verus should automatically prove that subrange concatenation equals the original sequence
    assert(firstPart + secondPart == arr@.subrange(0, L as int) + arr@.subrange(L as int, arr.len() as int));
    
    // The key insight: concatenating adjacent subranges gives back the original sequence
    assert(arr@.subrange(0, L as int) + arr@.subrange(L as int, arr.len() as int) == arr@);
    
    (firstPart, secondPart)
}

}