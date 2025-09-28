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
/* helper modified by LLM (iteration 5): fix invariant conditions and postcondition satisfaction */
fn find_smallest_even_index(arr: &Vec<i8>) -> (result: Option<(i8, usize)>)
    ensures
        arr@.len() == 0 ==> result.is_none(),
        !has_even_value(arr@.map_values(|x: i8| x as int)) ==> result.is_none(),
        has_even_value(arr@.map_values(|x: i8| x as int)) ==> result.is_some(),
        result.is_some() ==> {
            let (val, idx) = result.unwrap();
            &&& (0 <= (idx as int) && (idx as int) < (arr@.len() as int))
            &&& arr@[idx as int] as int == val as int
            &&& val as int % 2 == 0
            &&& forall|i: int| 0 <= i < arr@.len() && arr@[i] as int % 2 == 0 ==> val as int <= arr@[i] as int
            &&& forall|i: int| 0 <= i < arr@.len() && arr@[i] as int % 2 == 0 && arr@[i] as int == val as int ==> (idx as int) <= i
        }
{
    let mut min_even: Option<i8> = None;
    let mut min_index: Option<usize> = None;
    
    for i in 0..arr.len()
        invariant
            min_even.is_some() ==> min_index.is_some(),
            min_even.is_some() ==> {
                let idx = min_index.unwrap();
                &&& 0 <= idx < arr.len()
                &&& arr@[idx as int] % 2 == 0
                &&& forall|j: int| 0 <= j < i && arr@[j] % 2 == 0 ==> min_even.unwrap() as int <= arr@[j]
                &&& forall|j: int| 0 <= j < i && arr@[j] % 2 == 0 && arr@[j] as int == min_even.unwrap() as int ==> (idx as int) <= j
            }
    {
        let x = arr[i];
        if x % 2 == 0 {
            if min_even.is_none() || x < min_even.unwrap() {
                min_even = Some(x);
                min_index = Some(i);
            } else if x == min_even.unwrap() && i < min_index.unwrap() {
                // Update index to ensure we get the smallest index for equal values
                min_index = Some(i);
            }
        }
    }
    
    if min_even.is_some() && min_index.is_some() {
        Some((min_even.unwrap(), min_index.unwrap()))
    } else {
        None
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
{
    /* code modified by LLM (iteration 5): fix index bounds checking and result construction */
    if arr.len() == 0 {
        vec![]
    } else {
        let result = find_smallest_even_index(&arr);
        if let Some((val, idx)) = result {
            proof {
                assert(0 <= (idx as int) && (idx as int) < (arr@.len() as int));
                assert(arr@[idx as int] as int == val as int);
            }
            vec![val, idx as i8]
        } else {
            vec![]
        }
    }
}
// </vc-code>


}

fn main() {}