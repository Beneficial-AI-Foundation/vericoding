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
    proof {
        // These assertions help Verus verify the postconditions
        assert(firstPart.len() == L);
        assert(secondPart.len() == arr.len() - L);
        
        // Use the subrange concatenation lemma
        assert(arr@.subrange(0, L as int) + arr@.subrange(L as int, arr.len() as int) == arr@) by {
            // Verus has built-in knowledge about subrange concatenation
            assert(0 <= L as int <= arr.len() as int);
        };
    }
    
    (firstPart, secondPart)
}

}