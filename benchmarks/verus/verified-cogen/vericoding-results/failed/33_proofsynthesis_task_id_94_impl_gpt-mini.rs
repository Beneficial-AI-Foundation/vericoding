// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): spec accessor for second element using int index */
spec fn second_at(arr: &Vec<Vec<i32>>, i: int) -> i32 { arr[i as usize][1] }
// </vc-helpers>

// <vc-spec>
fn min_second_value_first(arr: &Vec<Vec<i32>>) -> (first_of_min_second: i32)

    requires
        arr.len() > 0,
        forall|i: int| 0 <= i < arr.len() ==> #[trigger] arr[i].len() >= 2,

    ensures
        exists|i: int|
            0 <= i < arr.len() && first_of_min_second == #[trigger] arr[i][0] && (forall|j: int|
                0 <= j < arr.len() ==> (arr[i][1] <= #[trigger] arr[j][1])),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): use int indices with usize casts for indexing and proper invariants/proof */
    let mut min_idx: int = 0 as int;
    let mut i: int = 1 as int;
    while i < arr.len() as int
        invariant
            0 <= min_idx && min_idx < arr.len() as int,
            0 <= i && i <= arr.len() as int,
            forall|t: int| 0 <= t < i ==> arr[min_idx as usize][1] <= arr[t as usize][1],
        decreases arr.len() as int - i
    {
        if arr[i as usize][1] < arr[min_idx as usize][1] {
            min_idx = i;
        }
        i = i + 1 as int;
    }
    let result: i32 = arr[min_idx as usize][0];
    proof {
        assert(0 <= min_idx && min_idx < arr.len() as int);
        assert(forall|t: int| 0 <= t < arr.len() as int ==> arr[min_idx as usize][1] <= arr[t as usize][1]);
        assert(exists|i0: int| 0 <= i0 < arr.len() as int && result == arr[i0 as usize][0] && (forall|j: int| 0 <= j < arr.len() as int ==> arr[i0 as usize][1] <= arr[j as usize][1]));
    }
    result
}
// </vc-code>

}
fn main() {}