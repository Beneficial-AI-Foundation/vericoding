use vstd::prelude::*;

fn main() {}

verus! {

fn has_common_element(list1: &Vec<i32>, list2: &Vec<i32>) -> (result: bool)
    ensures
        result == (exists|i: int, j: int|
            0 <= i < list1.len() && 0 <= j < list2.len() && (list1[i] == list2[j])),
{
    /* code modified by LLM (iteration 3): Fixed outer loop invariant to properly handle bounds */
    for i in 0..list1.len()
        invariant
            forall|ii: int, jj: int|
                0 <= ii < i && 0 <= jj < list2.len() ==> list1[ii] != list2[jj],
    {
        /* code modified by LLM (iteration 3): Fixed inner loop invariant to use current i index with proper bounds */
        for j in 0..list2.len()
            invariant
                i < list1.len(),
                forall|jj: int|
                    0 <= jj < j ==> list1[i as int] != list2[jj],
        {
            /* code modified by LLM (iteration 3): Removed unnecessary assertion and fixed bounds access */
            if list1[i] == list2[j] {
                return true;
            }
        }
    }
    /* code modified by LLM (iteration 3): Added proper assertion to prove no common elements exist */
    assert(forall|ii: int, jj: int| 0 <= ii < list1.len() && 0 <= jj < list2.len() ==> list1[ii] != list2[jj]);
    false
}

} // verus!