use vstd::prelude::*;


verus! {

fn min_second_value_first(arr: &Vec<Vec<i32>>) -> (first_of_min_second: i32)
    // pre-conditions-start
    requires
        arr.len() > 0,
        forall|i: int| 0 <= i < arr.len() ==> #[trigger] arr[i].len() >= 2,
    // pre-conditions-end
    // post-conditions-start
    ensures
        exists|i: int|
            0 <= i < arr.len() && first_of_min_second == #[trigger] arr[i][0] && (forall|j: int|
                0 <= j < arr.len() ==> (arr[i][1] <= #[trigger] arr[j][1])),
    // post-conditions-end
{
    return 0;  // TODO: Remove this line and implement the function body
}

} // verus!

fn main() {}
