use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn AddTupleToList(l: seq<(int, int)>, t: (int, int)) -> (r: seq<(int, int)>)
    ensures
        r.len() == l.len() + 1,
        r.spec_index(r.len() - 1) == t,
        forall|i: int| 0 <= i < l.len() ==> r.spec_index(i) == l.spec_index(i)
{
    let result = l + seq![t];
    
    // Proof assertions to help Verus verify the postconditions
    assert(result.len() == l.len() + seq![t].len());
    assert(seq![t].len() == 1);
    assert(result.len() == l.len() + 1);
    
    // Prove that the last element is t
    assert(result.spec_index(result.len() - 1) == t);
    
    // Prove that all original elements are preserved
    assert(forall|i: int| 0 <= i < l.len() ==> result.spec_index(i) == l.spec_index(i));
    
    result
}

}