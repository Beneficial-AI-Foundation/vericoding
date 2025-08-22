use vstd::prelude::*;

fn main() {
}

verus! {

fn find_first_odd(arr: &Vec<u32>) -> (index: Option<usize>)
    ensures
        if let Some(idx) = index {
            idx < arr.len() && arr@[idx as int] % 2 != 0 && forall|k: int| 0 <= k < idx as int ==> (arr@[k] % 2 == 0)
        } else {
            forall|k: int| 0 <= k < arr.len() as int ==> (arr@[k] % 2 == 0)
        },
{
    let mut index = 0;
    while index < arr.len()
        invariant
            0 <= index <= arr.len(),
            forall|k: int| 0 <= k < index as int ==> (arr@[k] % 2 == 0),
    {
        /* code modified by LLM (iteration 2): use regular indexing in executable code, ghost operations only in specs */
        if arr[index] % 2 != 0 {
            return Some(index);
        }
        index += 1;
    }
    None
}

} // verus!