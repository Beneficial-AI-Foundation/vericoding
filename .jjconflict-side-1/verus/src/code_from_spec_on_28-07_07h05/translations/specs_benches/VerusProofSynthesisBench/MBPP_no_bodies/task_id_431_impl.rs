use vstd::prelude::*;

verus! {

fn has_common_element(list1: &Vec<i32>, list2: &Vec<i32>) -> (result: bool)
    // post-conditions-start
    ensures
        result == (exists|i: int, j: int|
            0 <= i < list1.len() && 0 <= j < list2.len() && (list1[i] == list2[j])),
    // post-conditions-end
{
    for i in 0..list1.len()
        invariant
            forall|ii: int, j: int|
                0 <= ii < i && 0 <= j < list2.len() ==> list1[ii] != list2[j],
    {
        for j in 0..list2.len()
            invariant
                /* code modified by LLM (iteration 2): fixed invariant to ensure i is within bounds when accessing list1 */
                i < list1.len() && forall|jj: int|
                    0 <= jj < j ==> list1[i as int] != list2[jj],
        {
            /* code modified by LLM (iteration 1): added bounds check to ensure safe array access */
            if i < list1.len() && j < list2.len() && list1[i] == list2[j] {
                /* code modified by LLM (iteration 1): added assertion to help prove postcondition */
                assert(exists|ii: int, jj: int|
                    0 <= ii < list1.len() && 0 <= jj < list2.len() && (list1[ii] == list2[jj])) by {
                    assert(0 <= i < list1.len() && 0 <= j < list2.len() && list1[i as int] == list2[j as int]);
                }
                return true;
            }
        }
    }
    /* code modified by LLM (iteration 1): added assertion to prove postcondition when returning false */
    assert(forall|i: int, j: int|
        0 <= i < list1.len() && 0 <= j < list2.len() ==> list1[i] != list2[j]) by {
        assert(forall|ii: int, j: int|
            0 <= ii < list1.len() && 0 <= j < list2.len() ==> list1[ii] != list2[j]);
    }
    false
}

} // verus!

fn main() {}