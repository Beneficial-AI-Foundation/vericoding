use vstd::prelude::*;


verus! {

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
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
// </vc-spec>

// <vc-code>
{
    assert!(arr.len() > 0);
    assert!(forall|i: int| 0 <= i < arr.len() ==> #[trigger] arr[i].len() >= 2);
    let mut min_second = arr[0][1];
    let mut first_of_min = arr[0][0];
    let mut i: usize = 1;

    while i < arr.len()
        invariant
            1 <= i <= arr.len(),
            arr.len() > 0,
            forall|j: usize| j < arr.len() ==> #[trigger] arr[j].len() >= 2,
            exists|k: usize| k < i && first_of_min == arr[k][0] && 
                forall|j: usize| j < i ==> min_second <= arr[j][1],
        decreases arr.len() - i
    {
        if arr[i][1] < min_second {
            min_second = arr[i][1];
            first_of_min = arr[i][0];
        }
        i = i + 1;
    }
    first_of_min
}
// </vc-code>

} // verus!

fn main() {}