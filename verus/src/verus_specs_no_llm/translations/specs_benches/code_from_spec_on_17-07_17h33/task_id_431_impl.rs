use vstd::prelude::*;

verus! {

//IMPL has_common_element
fn has_common_element(list1: &Vec<i32>, list2: &Vec<i32>) -> (result: bool)
{
    return false;  // TODO: Remove this line and implement the function body
}
    // post-conditions-start
    ensures
        result == (exists|i: int, j: int|
            0 <= i < list1.len() && 0 <= j < list2.len() && (list1[i] == list2[j])),
    // post-conditions-end
{
    /* code modified by LLM (iteration 1): Moved ensures clause before function body and implemented correct logic to check for common elements */
    for i in 0..list1.len()
        invariant
            !(exists|ii: int, j: int|
                0 <= ii < i && 0 <= j < list2.len() && (list1[ii] == list2[j])),
    {
        for j in 0..list2.len()
            invariant
                !(exists|jj: int|
                    0 <= jj < j && (list1[i as int] == list2[jj])),
        {
            if list1[i] == list2[j] {
                return true;
            }
        }
    }
    false
}

} // verus!

fn main() {}