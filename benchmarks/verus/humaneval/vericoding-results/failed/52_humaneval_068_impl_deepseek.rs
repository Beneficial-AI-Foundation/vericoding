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

proof fn lemma_smallest_even_value_helper_properties(arr: Seq<int>, index: int, current_min: int)
    requires
        valid_input(arr),
        0 <= index <= arr.len(),
        current_min == -1 || (current_min >= 0 && current_min % 2 == 0),
        forall|i: int| 0 <= i < index && arr[i] % 2 == 0 ==> current_min == -1 || current_min <= arr[i]
    ensures
        smallest_even_value_helper(arr, index, current_min) == -1 || smallest_even_value_helper(arr, index, current_min) % 2 == 0,
        smallest_even_value_helper(arr, index, current_min) == -1 ==> !exists|i: int| index <= i < arr.len() && arr[i] % 2 == 0,
        smallest_even_value_helper(arr, index, current_min) != -1 ==> (
            exists|i: int| index <= i < arr.len() && arr[i] == smallest_even_value_helper(arr, index, current_min) && arr[i] % 2 == 0
            && forall|j: int| index <= j < arr.len() && arr[j] % 2 == 0 ==> smallest_even_value_helper(arr, index, current_min) <= arr[j]
        )
    decreases arr.len() - index
{
    if index >= arr.len() {
        // Base case: no more elements to process
    } else {
        if arr[index] % 2 == 0 {
            if current_min == -1 || arr[index] < current_min {
                lemma_smallest_even_value_helper_properties(arr, index + 1, arr[index]);
            } else {
                lemma_smallest_even_value_helper_properties(arr, index + 1, current_min);
            }
        } else {
            lemma_smallest_even_value_helper_properties(arr, index + 1, current_min);
        }
    }
}

proof fn lemma_first_index_properties(arr: Seq<int>, value: int)
    requires
        valid_input(arr),
        value >= 0,
        value % 2 == 0,
        exists|i: int| 0 <= i < arr.len() && arr[i] == value
    ensures
        0 <= first_index_of_value(arr, value) < arr.len(),
        arr[first_index_of_value(arr, value)] == value,
        forall|i: int| 0 <= i < first_index_of_value(arr, value) ==> arr[i] != value
    decreases arr.len()
{
    if arr.len() > 0 {
        if arr[0] == value {
            // Found at first position
        } else {
            lemma_first_index_properties(arr.subrange(1, arr.len() as int), value);
        }
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
    /* code modified by LLM (iteration 5): Fix compilation error by removing @ operator */
    let mut result = Vec::new();
    
    proof {
        let arr_seq = arr.view();
        let arr_seq_spec = arr_seq.map_values(|x: i8| x as int);
        lemma_smallest_even_value_helper_properties(arr_seq_spec, 0, -1);
        let min_even_spec = smallest_even_value(arr_seq_spec);
        
        if min_even_spec != -1 {
            lemma_first_index_properties(arr_seq_spec, min_even_spec);
        }
    }
    
    // Find minimum even value and its index in executable code
    let mut min_even: Option<i8> = None;
    let mut min_index: usize = 0;
    
    for i in 0..arr.len() {
        let val = arr[i];
        if val % 2 == 0 {
            match min_even {
                None => {
                    min_even = Some(val);
                    min_index = i;
                }
                Some(current_min) if val < current_min => {
                    min_even = Some(val);
                    min_index = i;
                }
                _ => {}
            }
        }
    }
    
    if let Some(min_val) = min_even {
        result.push(min_val);
        result.push(min_index as i8);
    }
    
    result
}
// </vc-code>


}

fn main() {}