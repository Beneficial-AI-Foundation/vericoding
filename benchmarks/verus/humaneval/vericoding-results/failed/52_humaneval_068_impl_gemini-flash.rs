// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(arr: Seq<int>) -> bool {
    forall|i: int| 0 <= i < arr.len() ==> arr[i] >= 0
}

spec fn has_even_value(arr: Seq<int>) -> bool {
    exists|i: int| 0 <= i < arr.len() && arr[i] % 2 == 0
}

spec fn smallest_even_value(arr: Seq<int>) -> int {
    smallest_even_value_helper(arr, 0, -1)
}

spec fn smallest_even_value_helper(arr: Seq<int>, index: int, current_min: int) -> int
    decreases arr.len() - index
{
    if index >= arr.len() {
        current_min
    } else if arr[index] % 2 == 0 {
        if current_min == -1 || arr[index] < current_min {
            smallest_even_value_helper(arr, index + 1, arr[index])
        } else {
            smallest_even_value_helper(arr, index + 1, current_min)
        }
    } else {
        smallest_even_value_helper(arr, index + 1, current_min)
    }
}

spec fn first_index_of_value(arr: Seq<int>, value: int) -> int
    decreases arr.len()
{
    if arr.len() > 0 && arr[0] == value {
        0
    } else if arr.len() > 0 {
        1 + first_index_of_value(arr.subrange(1, arr.len() as int), value)
    } else {
        0
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): Removed all helper functions since they were not needed and caused compilation issues or verification failures. */
// </vc-helpers>

// <vc-spec>
fn pluck(arr: Vec<i8>) -> (result: Vec<i8>)
    requires 
        valid_input(arr@.map_values(|x: i8| x as int))
    ensures 
        arr@.len() == 0 ==> result@.len() == 0,
        !has_even_value(arr@.map_values(|x: i8| x as int)) ==> result@.len() == 0,
        has_even_value(arr@.map_values(|x: i8| x as int)) ==> result@.len() == 2,
        result@.len() == 2 ==> (0 <= (result@[1] as int) && (result@[1] as int) < (arr@.len() as int)),
        result@.len() == 2 ==> arr@[result@[1] as int] as int == result@[0] as int,
        result@.len() == 2 ==> result@[0] as int % 2 == 0,
        result@.len() == 2 ==> forall|i: int| 0 <= i < arr@.len() && arr@[i] as int % 2 == 0 ==> result@[0] as int <= arr@[i] as int,
        result@.len() == 2 ==> forall|i: int| 0 <= i < arr@.len() && arr@[i] as int % 2 == 0 && arr@[i] as int == result@[0] as int ==> result@[1] as int <= i
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): Changed map_values closure to use `as int` only when the value is actually an int type. Added checks for empty arrays and no even values. Explicitly proved smallest_val and smallest_val_idx. */
    let s_arr = arr@.map_values(|x: i8| x as int);

    if arr.len() == 0 {
        return Vec::new();
    }

    if !has_even_value(s_arr) {
        return Vec::new();
    }

    let smallest_val = smallest_even_value(s_arr);
    
    let mut smallest_val_idx: int = 0;
    let mut i: int = 0;

    while i < s_arr.len()
        invariant 
            0 <= i <= s_arr.len(),
            valid_input(s_arr),
            has_even_value(s_arr),
            smallest_val == smallest_even_value(s_arr),
            0 <= smallest_val_idx < i || (smallest_val_idx == 0 && i == 0),
            s_arr[smallest_val_idx] == smallest_val,
            s_arr[smallest_val_idx] % 2 == 0,
            forall|k: int| 0 <= k < i && (s_arr[k] % 2 == 0) && (s_arr[k] == smallest_val) ==> (smallest_val_idx <= k),
        decreases s_arr.len() - i
    {
        if s_arr[i] % 2 == 0 && s_arr[i] == smallest_val {
            smallest_val_idx = i;
        }
        i = i + 1;
    }
    
    let mut result = Vec::new();
    result.push(smallest_val as i8);
    result.push(smallest_val_idx as i8);

    result
}
// </vc-code>


}

fn main() {}