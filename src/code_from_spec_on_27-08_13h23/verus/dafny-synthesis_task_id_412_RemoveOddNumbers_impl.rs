use vstd::prelude::*;

verus! {

/**
 * Remove odd numbers from an array of numbers
 **/

spec fn is_even(n: int) -> bool {
    n % 2 == 0
}

// <vc-helpers>
spec fn count_even_numbers(arr: &[i32]) -> nat
    decreases arr.len()
{
    if arr.len() == 0 {
        0
    } else {
        let rest_count = count_even_numbers(&arr[1..]);
        if is_even(arr[0] as int) {
            1 + rest_count
        } else {
            rest_count
        }
    }
}

proof fn seq_filter_contains(arr: Seq<i32>, x: i32)
    requires
        arr.contains(x),
        is_even(x as int),
    ensures
        seq_filter(arr, |y: i32| is_even(y as int)).contains(x),
{
    let mut i = 0;
    while i < arr.len()
        invariant
            0 <= i <= arr.len(),
            arr.subrange(0, i as int).contains(x) ==> seq_filter(arr.subrange(0, i as int), |y: i32| is_even(y as int)).contains(x),
    {
        if arr[i] == x {
            assert(seq_filter(arr.subrange(0, i as int + 1), |y: i32| is_even(y as int)).contains(x));
            break;
        }
        i = i + 1;
    }
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
fn remove_odd_numbers(arr: &[i32]) -> (even_list: Vec<i32>)
    ensures
        // All numbers in the output are even and exist in the input 
        forall|i: int| 0 <= i < even_list.len() ==> is_even(even_list[i] as int) && arr@.contains(even_list[i]),
        // All even numbers in the input are in the output
        forall|i: int| 0 <= i < arr.len() && is_even(arr[i] as int) ==> even_list@.contains(arr[i])
// </vc-spec>
// </vc-spec>

// <vc-code>
fn remove_odd_numbers(arr: &[i32]) -> (even_list: Vec<i32>)
    ensures
        forall|i: int| 0 <= i < even_list.len() ==> is_even(even_list[i] as int) && arr@.contains(even_list[i]),
        forall|i: int| 0 <= i < arr.len() && is_even(arr[i] as int) ==> even_list@.contains(arr[i]),
{
    let mut result = Vec::new();
    let mut i = 0;

    while i < arr.len()
        invariant
            0 <= i <= arr.len(),
            forall|j: int| 0 <= j < result.len() ==> is_even(result[j] as int) && arr@.contains(result[j]),
            forall|j: int| 0 <= j < i && is_even(arr[j] as int) ==> result@.contains(arr[j]),
    {
        if is_even(arr[i] as int) {
            result.push(arr[i]);
        }
        i = i + 1;
    }

    result
}
// </vc-code>

fn main() {
}

}