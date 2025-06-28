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
            // All processed elements that should be in result are in result
            forall|j: int| 0 <= j < i ==> 
                ((a.contains(a.spec_index(j)) && !b.contains(a.spec_index(j))) ==> result.contains(a.spec_index(j))),
            // All elements in result come from the processed portion or are valid candidates
            forall|x: int| result.contains(x) ==> a.contains(x),
    {
        let elem = a.spec_index(i);
        if !b.contains(elem) && !result.contains(elem) {
            result = result.push(elem);
        }
        i = i + 1;
    }
    
    result
}

}