use vstd::prelude::*;

fn main() {}

verus! {

fn find_first_odd(arr: &Vec<u32>) -> (index: Option<usize>)
    ensures
        if let Some(idx) = index {
            idx < arr.len() && arr@[idx as int] % 2 == 1 && forall|k: int| 0 <= k < idx as int ==> (arr@[k] % 2 == 0)
        } else {
            forall|k: int| 0 <= k < arr.len() ==> (arr@[k] % 2 == 0)
        },
{
    let mut index = 0;
    /* code modified by LLM (iteration 1): added decreases clause to prove loop termination */
    while index < arr.len()
        invariant
            0 <= index <= arr.len(),
            forall|k: int| 0 <= k < index as int ==> (arr@[k] % 2 == 0),
        decreases arr.len() - index,
    {
        /* code modified by LLM (iteration 2): fixed array access using regular indexing instead of @ operator in exec code */
        if arr[index] % 2 != 0 {
            return Some(index);
        }
        index += 1;
    }
    None
}

} // verus!