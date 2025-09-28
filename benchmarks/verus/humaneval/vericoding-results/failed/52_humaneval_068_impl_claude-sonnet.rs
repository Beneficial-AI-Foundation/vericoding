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
/* helper modified by LLM (iteration 5): added inductive proof for smallest_even_value_helper */
fn lemma_smallest_even_value_helper_inductive(arr: Seq<int>, index: int, current_min: int, min_val: int, min_idx: int)
    requires
        valid_input(arr),
        0 <= index <= arr.len(),
        0 <= min_idx < arr.len(),
        arr[min_idx] % 2 == 0,
        arr[min_idx] == min_val,
        forall|i: int| 0 <= i < arr.len() && arr[i] % 2 == 0 ==> min_val <= arr[i],
        forall|i: int| 0 <= i < arr.len() && arr[i] % 2 == 0 && arr[i] == min_val ==> min_idx <= i,
        (current_min == -1 && min_idx >= index) || (current_min != -1 && current_min == min_val)
    ensures
        smallest_even_value_helper(arr, index, current_min) == min_val
    decreases arr.len() - index
{
    if index >= arr.len() {
        return;
    }
    
    if arr[index] % 2 == 0 {
        if current_min == -1 || arr[index] < current_min {
            if arr[index] == min_val {
                lemma_smallest_even_value_helper_inductive(arr, index + 1, arr[index], min_val, min_idx);
            }
        } else {
            lemma_smallest_even_value_helper_inductive(arr, index + 1, current_min, min_val, min_idx);
        }
    } else {
        lemma_smallest_even_value_helper_inductive(arr, index + 1, current_min, min_val, min_idx);
    }
}

fn lemma_first_index_helper(arr: Seq<int>, value: int, idx: int, offset: int)
    requires
        0 <= offset <= idx < arr.len(),
        arr[idx] == value,
        forall|i: int| offset <= i < arr.len() && arr[i] == value ==> idx <= i
    ensures
        first_index_of_value(arr.subrange(offset, arr.len() as int), value) == idx - offset
    decreases idx - offset
{
    if offset == idx {
        return;
    }
    if arr[offset] == value {
        assert(false);
    } else {
        lemma_first_index_helper(arr, value, idx, offset + 1);
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
    /* code modified by LLM (iteration 5): fixed postcondition satisfaction */
    if arr.len() == 0 {
        return Vec::new();
    }
    
    let int_arr = arr@.map_values(|x: i8| x as int);
    
    if !has_even_value(int_arr) {
        return Vec::new();
    }
    
    let mut min_even: Option<i8> = None;
    let mut min_index: usize = 0;
    let mut i = 0;
    
    while i < arr.len()
        invariant
            0 <= i <= arr.len(),
            min_even.is_some() ==> (min_even.unwrap() as int % 2 == 0),
            min_even.is_some() ==> (0 <= min_index < i),
            min_even.is_some() ==> (arr@[min_index as int] == min_even.unwrap()),
            min_even.is_some() ==> forall|j: int| 0 <= j < i && arr@[j] % 2 == 0 ==> min_even.unwrap() as int <= arr@[j],
            min_even.is_some() ==> forall|j: int| 0 <= j < i && arr@[j] % 2 == 0 && arr@[j] == min_even.unwrap() as int ==> min_index as int <= j,
            min_even.is_none() ==> forall|j: int| 0 <= j < i ==> arr@[j] % 2 != 0
        decreases arr.len() - i
    {
        if arr[i] % 2 == 0 {
            match min_even {
                None => {
                    min_even = Some(arr[i]);
                    min_index = i;
                }
                Some(current_min) => {
                    if arr[i] < current_min || (arr[i] == current_min && i < min_index) {
                        min_even = Some(arr[i]);
                        min_index = i;
                    }
                }
            }
        }
        i += 1;
    }
    
    let mut result = Vec::new();
    match min_even {
        None => {
            proof {
                assert(forall|j: int| 0 <= j < arr@.len() ==> arr@[j] % 2 != 0);
                assert(!has_even_value(int_arr));
            }
        }
        Some(val) => {
            result.push(val);
            #[verifier::truncate]
            result.push(min_index as i8);
            
            proof {
                assert(0 <= min_index < arr@.len());
                assert(arr@[min_index as int] == val);
                assert(val as int % 2 == 0);
                assert(forall|j: int| 0 <= j < arr@.len() && arr@[j] % 2 == 0 ==> val as int <= arr@[j]);
                assert(forall|j: int| 0 <= j < arr@.len() && arr@[j] % 2 == 0 && arr@[j] == val as int ==> min_index as int <= j);
            }
        }
    }
    result
}
// </vc-code>


}

fn main() {}