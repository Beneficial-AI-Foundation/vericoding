use vstd::prelude::*;

verus! {

fn get_first_elements(arr: &Vec<Vec<i32>>) -> (result: Vec<i32>)
    requires
        forall|i: int| 0 <= i < arr.len() ==> #[trigger] arr[i].len() > 0,
    ensures
        arr.len() == result.len(),
        forall|i: int| 0 <= i < arr.len() ==> #[trigger] result[i] == #[trigger] arr[i][0],
{
    let mut first_elem_arr: Vec<i32> = Vec::new();
    let mut index = 0;
    while index < arr.len()
        invariant
            0 <= index <= arr.len(),
            first_elem_arr.len() == index,
            forall|i: int| 0 <= i < arr.len() ==> #[trigger] arr[i].len() > 0,
            forall|k: int| 0 <= k < index ==> #[trigger] first_elem_arr[k] == #[trigger] arr[k][0],
    {
        let seq = &arr[index];
        assert(seq.len() > 0);
        first_elem_arr.push(seq[0]);
        index += 1;
    }
    first_elem_arr
}

fn main() {}

} // verus!
