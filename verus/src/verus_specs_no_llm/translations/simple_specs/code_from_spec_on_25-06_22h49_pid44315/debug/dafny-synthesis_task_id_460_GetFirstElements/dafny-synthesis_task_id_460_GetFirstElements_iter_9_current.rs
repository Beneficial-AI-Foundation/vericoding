use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn GetFirstElements(lst: Seq<Seq<int>>) -> (result: Seq<int>)
    requires
        forall|i: int| 0 <= i < lst.len() ==> lst.spec_index(i).len() > 0
    ensures
        result.len() == lst.len(),
        forall|i: int| 0 <= i < result.len() ==> result.spec_index(i) == lst.spec_index(i).spec_index(0)
{
    let mut result = Seq::empty();
    let mut i: usize = 0;
    
    while i < lst.len()
        invariant
            0 <= i <= lst.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result.spec_index(j) == lst.spec_index(j).spec_index(0)
    {
        proof {
            assert(0 <= i < lst.len());
            assert(lst.spec_index(i as int).len() > 0);
        }
        
        // Use .index() for executable access to sequence elements
        let inner_seq = lst.index(i as int);
        let first_elem = inner_seq.index(0int);
        
        result = result.push(first_elem);
        i = i + 1;
    }
    
    result
}

}