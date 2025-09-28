// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn arrays_equal_at_indices<T>(a1: &Vec<T>, a2: &Vec<T>, end: int) -> bool
    where T: PartialEq<T>,
{
    forall|i: int| 0 <= i < end ==> a1@[i] == a2@[i]
}

/* helper modified by LLM (iteration 5): fixed preconditions and made lemmas executable */
fn lemma_arrays_equal_extend<T>(a1: &Vec<T>, a2: &Vec<T>, end: int)
    where T: PartialEq<T>,
    requires
        0 <= end < a1.len() as int,
        a1.len() == a2.len(),
        arrays_equal_at_indices(a1, a2, end),
        a1@[end] == a2@[end],
    ensures arrays_equal_at_indices(a1, a2, end + 1)
{
}

fn lemma_arrays_equal_complete<T>(a1: &Vec<T>, a2: &Vec<T>)
    where T: PartialEq<T>,
    requires
        a1.len() == a2.len(),
        arrays_equal_at_indices(a1, a2, a1.len() as int),
    ensures forall|i: int| 0 <= i < a1.len() as int ==> a1@[i] == a2@[i]
{
}
// </vc-helpers>

// <vc-spec>
fn array_equal<T>(a1: &Vec<T>, a2: &Vec<T>) -> (result: bool)
    where T: PartialEq<T>,
    requires a1.len() == a2.len(),
    ensures 
        result == true <==> (forall|i: int| 0 <= i < a1.len() as int ==> a1@[i] == a2@[i]) &&
        (a1.len() == 0 ==> result == true) &&
        (exists|i: int| 0 <= i < a1.len() as int && !(a1@[i] == a2@[i]) ==> result == false)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed postcondition satisfaction by simplifying ensures clause logic */
    if a1.len() == 0 {
        return true;
    }
    
    let mut i = 0;
    
    while i < a1.len()
        invariant
            0 <= i <= a1.len(),
            a1.len() == a2.len(),
            arrays_equal_at_indices(a1, a2, i as int),
        decreases a1.len() - i
    {
        if !(a1[i] == a2[i]) {
            return false;
        }
        
        lemma_arrays_equal_extend(a1, a2, i as int);
        
        i = i + 1;
    }
    
    lemma_arrays_equal_complete(a1, a2);
    
    true
}
// </vc-code>

}
fn main() {}