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
/* helper modified by LLM (iteration 4): fixed type cast for subrange argument in first_index_of_value */
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
/* code modified by LLM (iteration 5): corrected assert statement cast for index comparison */
{
    let mut min_even: i8 = i8::MAX;
    let mut first_index: usize = 0;
    let mut found = false;
    let mut i: usize = 0;
    let arr_seq = arr@.map_values(|x: i8| x as int);
    while i < arr.len()
        invariant
            (i as int) <= arr_seq.len(),
            found ==> (0 <= (first_index as int) < (i as int) && arr_seq[(first_index as int)] == (min_even as int) && (min_even as int) % 2 == 0),
            found ==> forall|j: int| 0 <= j < (i as int) && arr_seq[j] % 2 == 0 ==> (min_even as int) <= arr_seq[j],
            found ==> forall|j: int| 0 <= j < (i as int) && arr_seq[j] == (min_even as int) ==> (first_index as int) <= j
        decreases arr.len() - i
    {
        let val = arr[i];
        if (val as int) % 2 == 0 {
            if !found || (val as int) < (min_even as int) {
                min_even = val;
                first_index = i;
                found = true;
            }
        }
        i += 1;
    }
    if found {
        let result = vec![min_even, first_index as i8];
        proof {
            assert(valid_input(arr_seq));
            assert((result@[0] as int) % 2 == 0);
            assert(forall|j: int| 0 <= j < arr_seq.len() && arr_seq[j] % 2 == 0 ==> (result@[0] as int) <= arr_seq[j]);
            assert((result@[1] as int) < (arr_seq.len() as int));
            assert(arr_seq[(result@[1] as int)] == (result@[0] as int));
            assert(forall|j: int| 0 <= j < arr_seq.len() && arr_seq[j] % 2 == 0 && arr_seq[j] == (result@[0] as int) ==> (result@[1] as int) <= j);
        }
        result
    } else {
        Vec::new()
    }
}
// </vc-code>


}

fn main() {}