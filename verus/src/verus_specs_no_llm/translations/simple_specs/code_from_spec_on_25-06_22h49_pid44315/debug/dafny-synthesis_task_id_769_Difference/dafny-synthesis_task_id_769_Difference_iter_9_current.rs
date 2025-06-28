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
                (a.contains(a.spec_index(j)) && !b.contains(a.spec_index(j))) ==> result.contains(a.spec_index(j)),
            // Everything in result comes from processed elements
            forall|x: int| result.contains(x) ==> 
                exists|j: int| 0 <= j < i && a.spec_index(j) == x,
    {
        let elem = a.spec_index(i);
        if !b.contains(elem) && !result.contains(elem) {
            result = result.push(elem);
        }
        i = i + 1;
    }
    
    // Prove the postcondition
    assert(i == a.len());
    
    // Prove soundness: everything in result is in a but not in b
    assert(forall|x: int| result.contains(x) ==> (a.contains(x) && !b.contains(x)));
    
    // Prove no duplicates
    assert(forall|i: int, j: int| 0 <= i < j < result.len() ==> result.spec_index(i) != result.spec_index(j));
    
    // Prove completeness: if x is in a but not in b, then x is in result
    assert(forall|x: int| (a.contains(x) && !b.contains(x)) ==> result.contains(x)) by {
        // For any x in a but not in b, there exists an index in a where x appears
        assert(forall|x: int| a.contains(x) ==> exists|k: int| 0 <= k < a.len() && a.spec_index(k) == x);
        
        // From the loop invariant at termination (i == a.len())
        assert(forall|j: int| 0 <= j < a.len() ==> 
            (a.contains(a.spec_index(j)) && !b.contains(a.spec_index(j))) ==> result.contains(a.spec_index(j)));
        
        // Therefore, for any x in a but not in b:
        // 1. x appears at some index k in a
        // 2. Since we processed all indices (i == a.len()), we processed index k
        // 3. Since x is in a but not in b, and a.spec_index(k) == x, we have result.contains(x)
    };
    
    result
}

}