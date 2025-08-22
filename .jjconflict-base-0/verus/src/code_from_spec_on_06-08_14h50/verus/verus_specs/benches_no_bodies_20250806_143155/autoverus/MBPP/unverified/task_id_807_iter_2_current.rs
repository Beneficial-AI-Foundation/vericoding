use vstd::prelude::*;

fn main() {}

verus! {

fn find_first_odd(arr: &Vec<u32>) -> (index: Option<usize>)
    ensures
        if let Some(idx) = index {
            /* code modified by LLM (iteration 1): fixed type conversion from usize to int for array access and comparison */
            idx < arr.len() && arr@[idx as int] % 2 == 1 && forall|k: int| 0 <= k < idx as int ==> (arr@[k] % 2 == 0)
        } else {
            forall|k: int| 0 <= k < arr.len() ==> (arr@[k] % 2 == 0)
        },
{
    let mut index = 0;
    while index < arr.len()
        invariant
            0 <= index <= arr.len(),
            /* code modified by LLM (iteration 1): fixed array access using @ operator and proper int conversion */
            forall|k: int| 0 <= k < index as int ==> (arr@[k] % 2 == 0),
    {
        /* code modified by LLM (iteration 1): fixed array access using @ operator */
        if arr@[index as int] % 2 != 0 {
            return Some(index);
        }
        index += 1;
    }
    None
}

} // verus!