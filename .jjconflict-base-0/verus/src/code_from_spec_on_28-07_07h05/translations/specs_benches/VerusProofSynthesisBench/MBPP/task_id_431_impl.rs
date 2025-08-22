use vstd::prelude::*;

verus! {

//IMPL has_common_element
fn has_common_element(list1: &Vec<i32>, list2: &Vec<i32>) -> (result: bool)
    // post-conditions-start
    ensures
        result == (exists|i: int, j: int|
            0 <= i < list1.len() && 0 <= j < list2.len() && (list1[i] == list2[j])),
    // post-conditions-end
{
    /* code modified by LLM (iteration 4): Fixed loop bounds and invariants to properly handle indexing */
    for i in 0..list1.len()
        invariant
            forall|ii: int, j: int|
                0 <= ii < i && 0 <= j < list2.len() ==> list1[ii] != list2[j],
    {
        /* code modified by LLM (iteration 4): Fixed inner loop invariant to use proper types */
        for j in 0..list2.len()
            invariant
                forall|jj: int|
                    0 <= jj < j ==> list1[i as int] != list2[jj],
        {
            /* code modified by LLM (iteration 4): Fixed assertion syntax for witness proof */
            if list1[i] == list2[j] {
                assert(exists|ii: int, jj: int|
                    0 <= ii < list1.len() && 0 <= jj < list2.len() && (list1[ii] == list2[jj])
                ) by {
                    assert(0 <= (i as int) && (i as int) < list1.len());
                    assert(0 <= (j as int) && (j as int) < list2.len());
                    assert(list1[i as int] == list2[j as int]);
                }
                return true;
            }
        }
    }
    false
}

} // verus!

fn main() {}