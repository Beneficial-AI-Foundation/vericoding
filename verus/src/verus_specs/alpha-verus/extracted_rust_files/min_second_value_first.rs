use vstd::prelude::*;

verus! {

fn min_second_value_first(arr: &Vec<Vec<i32>>) -> (first_of_min_second: i32)
    requires
        arr.len() > 0,
        forall|i: int| 0 <= i < arr.len() ==> #[trigger] arr[i].len() >= 2,
    ensures
        exists|i: int|
            0 <= i < arr.len() && first_of_min_second == #[trigger] arr[i][0] && (forall|j: int|
                0 <= j < arr.len() ==> (arr[i][1] <= #[trigger] arr[j][1])),
{
    let mut min_second_index = 0;
    let mut index = 0;

    while index < arr.len()
        invariant
            0 <= min_second_index < arr.len(),
            forall|i: int| 0 <= i < arr.len() ==> #[trigger] arr[i].len() >= 2,
            forall|k: int|
                0 <= k < index ==> (arr[min_second_index as int][1] <= #[trigger] arr[k][1]),
    {
        assert(arr[index as int].len() > 0);
        assert(arr[min_second_index as int].len() > 0);

        if arr[index][1] < arr[min_second_index][1] {
            min_second_index = index;
        }
        index += 1;
    }
    assert(arr[min_second_index as int].len() > 0);
    arr[min_second_index][0]
}

fn main() {}

} // verus!
