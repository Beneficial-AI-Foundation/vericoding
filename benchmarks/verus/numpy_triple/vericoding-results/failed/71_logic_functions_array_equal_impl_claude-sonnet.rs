// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): simplified spec function and added proper proof steps */
spec fn arrays_equal<T>(a1: &Vec<T>, a2: &Vec<T>) -> bool
    where T: PartialEq<T>
{
    a1.len() == a2.len() && forall|i: int| 0 <= i < a1.len() ==> a1@[i] == a2@[i]
}

proof fn lemma_empty_arrays_equal<T>(a1: &Vec<T>, a2: &Vec<T>)
    where T: PartialEq<T>
    requires a1.len() == 0, a2.len() == 0
    ensures arrays_equal(a1, a2)
{
}

proof fn lemma_found_diff_implies_not_equal<T>(a1: &Vec<T>, a2: &Vec<T>, idx: int)
    where T: PartialEq<T>
    requires 0 <= idx < a1.len(), a1.len() == a2.len(), !(a1@[idx] == a2@[idx])
    ensures !arrays_equal(a1, a2)
{
}

proof fn lemma_all_equal_implies_arrays_equal<T>(a1: &Vec<T>, a2: &Vec<T>)
    where T: PartialEq<T>
    requires 
        a1.len() == a2.len(),
        forall|i: int| 0 <= i < a1.len() ==> a1@[i] == a2@[i]
    ensures arrays_equal(a1, a2)
{
}
// </vc-helpers>

// <vc-spec>
fn array_equal<T>(a1: &Vec<T>, a2: &Vec<T>) -> (result: bool)
    where T: PartialEq<T>,
    requires a1.len() == a2.len(),
    ensures 
        result == true <==> (forall|i: int| 0 <= i < a1.len() ==> a1[i] == a2[i]) &&
        (a1.len() == 0 ==> result == true) &&
        (exists|i: int| 0 <= i < a1.len() && !(a1[i] == a2[i]) ==> result == false)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): added proper proof steps and fixed postcondition */
    let mut i = 0;
    while i < a1.len()
        invariant
            0 <= i <= a1.len(),
            a1.len() == a2.len(),
            forall|j: int| 0 <= j < i ==> a1@[j] == a2@[j]
        decreases a1.len() - i
    {
        if !(a1[i] == a2[i]) {
            proof {
                assert(!(a1@[i as int] == a2@[i as int]));
                lemma_found_diff_implies_not_equal(a1, a2, i as int);
            }
            return false;
        }
        i += 1;
    }
    proof {
        assert(forall|j: int| 0 <= j < a1.len() ==> a1@[j] == a2@[j]);
        lemma_all_equal_implies_arrays_equal(a1, a2);
    }
    true
}
// </vc-code>

}
fn main() {}