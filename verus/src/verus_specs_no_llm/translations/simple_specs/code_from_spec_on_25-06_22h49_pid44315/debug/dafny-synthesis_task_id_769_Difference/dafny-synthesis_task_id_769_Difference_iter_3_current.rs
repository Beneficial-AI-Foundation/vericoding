use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn Difference(a: Seq<int>, b: Seq<int>) -> (diff: Seq<int>)
    ensures
        forall|x: int| diff.contains(x) <==> (a.contains(x) && !b.contains(x)),
        forall|i: int, j: int| 0 <= i < j < diff.len() ==> diff.spec_index(i) != diff.spec_index(j)
{
    let mut result: Seq<int> = Seq::empty();
    let mut i = 0;
    
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            // Elements in result are valid (in a but not in b)
            forall|x: int| result.contains(x) ==> (a.contains(x) && !b.contains(x)),
            // No duplicates in result
            forall|k: int, l: int| 0 <= k < l < result.len() ==> result.spec_index(k) != result.spec_index(l),
            // All elements from processed indices that should be in diff are in result
            forall|j: int| 0 <= j < i ==> 
                ((a.contains(a.spec_index(j)) && !b.contains(a.spec_index(j))) ==> result.contains(a.spec_index(j))),
            // Every element in result corresponds to some processed index
            forall|x: int| result.contains(x) ==> 
                exists|j: int| 0 <= j < i && a.spec_index(j) == x,
    {
        let elem = a.spec_index(i);
        if !b.contains(elem) && !result.contains(elem) {
            result = result.push(elem);
            
            // Proof that the new element maintains no duplicates
            assert(forall|k: int| 0 <= k < result.len() - 1 ==> result.spec_index(k) != elem);
        }
        i = i + 1;
    }
    
    // After the loop, prove the completeness postcondition
    assert(forall|x: int| (a.contains(x) && !b.contains(x)) ==> result.contains(x)) by {
        // For any x in a but not in b, there exists some index j where a[j] == x
        // Since we processed all indices 0..a.len(), we must have processed j
        // and added x to result (if it wasn't already there)
    };
    
    // Prove the other direction of the biconditional
    assert(forall|x: int| result.contains(x) ==> (a.contains(x) && !b.contains(x)));
    
    result
}

}