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
/* helper modified by LLM (iteration 5): Added proper proof for smallest_even_correct lemma */
proof fn lemma_smallest_even_exists(arr: Seq<int>, index: nat)
    requires
        valid_input(arr),
        index < arr.len(),
        arr[index as int] % 2 == 0,
    ensures
        has_even_value(arr),
{
    assert(arr[index as int] % 2 == 0);
}

proof fn lemma_smallest_even_correct(arr: Seq<int>, min_val: int, min_idx: nat)
    requires
        valid_input(arr),
        min_idx < arr.len(),
        arr[min_idx as int] == min_val,
        min_val % 2 == 0,
        forall|i: int| 0 <= i < arr.len() && arr[i] % 2 == 0 ==> min_val <= arr[i],
    ensures
        has_even_value(arr),
        smallest_even_value(arr) == min_val,
    decreases arr.len()
{
    lemma_smallest_even_exists(arr, min_idx);
    lemma_smallest_even_helper_correct(arr, 0, -1, min_val, min_idx);
}

proof fn lemma_smallest_even_helper_correct(arr: Seq<int>, index: int, current_min: int, min_val: int, min_idx: nat)
    requires
        valid_input(arr),
        0 <= index <= arr.len(),
        min_idx < arr.len(),
        arr[min_idx as int] == min_val,
        min_val % 2 == 0,
        forall|i: int| 0 <= i < arr.len() && arr[i] % 2 == 0 ==> min_val <= arr[i],
        current_min == -1 || (current_min >= min_val && current_min % 2 == 0),
        forall|i: int| 0 <= i < index && arr[i] % 2 == 0 ==> current_min != -1 && current_min <= arr[i],
    ensures
        smallest_even_value_helper(arr, index, current_min) == min_val,
    decreases arr.len() - index
{
    if index >= arr.len() {
        if current_min != -1 {
            assert(current_min == min_val);
        } else {
            assert(false); // Contradiction: we know there's an even value
        }
    } else if arr[index] % 2 == 0 {
        if current_min == -1 || arr[index] < current_min {
            lemma_smallest_even_helper_correct(arr, index + 1, arr[index], min_val, min_idx);
        } else {
            lemma_smallest_even_helper_correct(arr, index + 1, current_min, min_val, min_idx);
        }
    } else {
        lemma_smallest_even_helper_correct(arr, index + 1, current_min, min_val, min_idx);
    }
}

proof fn lemma_first_index_correct(arr: Seq<int>, value: int, idx: nat)
    requires
        idx < arr.len(),
        arr[idx as int] == value,
        forall|i: int| 0 <= i < idx ==> arr[i] != value,
    ensures
        first_index_of_value(arr, value) == idx,
    decreases arr.len(),
{
    if idx == 0 {
        assert(arr[0] == value);
    } else {
        assert(arr[0] != value);
        lemma_first_index_correct(arr.subrange(1, arr.len() as int), value, (idx - 1) as nat);
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
    /* code modified by LLM (iteration 5): Fixed loop invariants to properly maintain all conditions */
    let mut min_even: Option<i8> = None;
    let mut min_index: usize = 0;
    let mut i: usize = 0;

    while i < arr.len()
        invariant
            i <= arr.len(),
            valid_input(arr@.map_values(|x: i8| x as int)),
            min_even.is_none() ==> forall|j: int| 0 <= j < i ==> arr@[j] as int % 2 != 0,
            min_even.is_some() ==> min_index < i,
            min_even.is_some() ==> min_index < arr.len(),
            min_even.is_some() ==> min_index <= 127,
            min_even.is_some() ==> arr@[min_index as int] == min_even.unwrap(),
            min_even.is_some() ==> min_even.unwrap() as int % 2 == 0,
            min_even.is_some() ==> forall|j: int| 0 <= j < i && arr@[j] as int % 2 == 0 ==> min_even.unwrap() as int <= arr@[j] as int,
            min_even.is_some() ==> forall|j: int| 0 <= j < min_index && arr@[j] as int % 2 == 0 && arr@[j] as int == min_even.unwrap() as int ==> false,
        decreases arr.len() - i
    {
        if arr[i] % 2 == 0 {
            if min_even.is_none() || arr[i] < min_even.unwrap() {
                if i <= 127 {
                    min_even = Some(arr[i]);
                    min_index = i;
                }
            }
        }
        i = i + 1;
    }

    if min_even.is_some() && min_index <= 127 {
        let mut result = Vec::new();
        result.push(min_even.unwrap());
        result.push(min_index as i8);
        proof {
            lemma_smallest_even_exists(arr@.map_values(|x: i8| x as int), min_index as nat);
            assert(has_even_value(arr@.map_values(|x: i8| x as int)));
            assert(result@.len() == 2);
            assert(result@[0] == min_even.unwrap());
            assert(0 <= min_index && min_index <= 127);
            assert(result@[1] == min_index as i8);
            assert(result@[1] as int == min_index as int);
            assert(forall|j: int| 0 <= j < arr.len() && arr@[j] as int % 2 == 0 ==> min_even.unwrap() as int <= arr@[j] as int);
            assert(forall|j: int| 0 <= j < arr.len() && arr@[j] as int % 2 == 0 && arr@[j] as int == min_even.unwrap() as int ==> min_index as int <= j);
            lemma_smallest_even_correct(arr@.map_values(|x: i8| x as int), min_even.unwrap() as int, min_index as nat);
        }
        result
    } else {
        proof {
            assert(!has_even_value(arr@.map_values(|x: i8| x as int)));
        }
        Vec::new()
    }
}
// </vc-code>


}

fn main() {}