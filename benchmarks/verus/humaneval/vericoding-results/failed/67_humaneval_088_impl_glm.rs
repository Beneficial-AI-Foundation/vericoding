// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(arr: Seq<int>) -> bool {
    forall|i: int| 0 <= i < arr.len() ==> arr[i] >= 0
}

spec fn is_ascending_sorted(s: Seq<int>) -> bool {
    forall|i: int, j: int| 0 <= i < j < s.len() ==> s[i] <= s[j]
}

spec fn is_descending_sorted(s: Seq<int>) -> bool {
    forall|i: int, j: int| 0 <= i < j < s.len() ==> s[i] >= s[j]
}

spec fn should_sort_ascending(arr: Seq<int>) -> bool {
    arr.len() > 1 && (arr[0] + arr[arr.len() - 1]) % 2 == 1
}

spec fn should_sort_descending(arr: Seq<int>) -> bool {
    arr.len() > 1 && (arr[0] + arr[arr.len() - 1]) % 2 == 0
}

spec fn correctly_sorted(arr: Seq<int>, result: Seq<int>) -> bool {
    (arr.len() <= 1 ==> result == arr) &&
    (should_sort_ascending(arr) ==> is_ascending_sorted(result)) &&
    (should_sort_descending(arr) ==> is_descending_sorted(result))
}

fn sort_ascending(arr: Seq<int>) -> (result: Seq<int>)
    ensures
        result.to_multiset() == arr.to_multiset(),
        is_ascending_sorted(result)
{
    assume(false);
    unreached()
}


fn sort_descending(arr: Seq<int>) -> (result: Seq<int>)
    ensures
        result.to_multiset() == arr.to_multiset(),
        is_descending_sorted(result)
{
    assume(false);
    unreached()
}

// </vc-preamble>

// <vc-helpers> 
/* helper modified by LLM (iteration 5): fixed syntax error in invariant by adding missing comma */
fn sort_ascending_vec(mut arr: Vec<i8>) -> (result: Vec<i8>)
    ensures
        result@.map(|i: int, x: i8| x as int).to_multiset() == old(&mut arr)@.map(|i: int, x: i8| x as int).to_multiset(),
        is_ascending_sorted(result@.map(|i: int, x: i8| x as int))
{
    let n = arr.len();
    let mut i = 0;
    while i < n - 1
        invariant
            0 <= i as int <= n as int - 1,
            arr@.map(|j: int, x: i8| x as int).to_multiset() == old(&mut arr)@.map(|j: int, x: i8| x as int).to_multiset(),
            forall|j: int, k: int| 0 <= j < k < i as int ==> arr@[j as int] <= arr@[k as int],
            forall|j: int| i as int <= j < n as int ==> forall|k: int| 0 <= k < i as int ==> arr@[k as int] <= arr@[j as int]
        decreases n - i
    {
        let mut min_index = i;
        let mut j = i + 1;
        while j < n
            invariant
                i as int <= j as int <= n as int,
                i as int <= min_index as int < n as int,
                forall|k: int| i as int <= k < j as int ==> arr@[min_index as int] <= arr@[k as int]
            decreases n - j
        {
            if arr[j] < arr[min_index] {
                min_index = j;
            }
            j = j + 1;
        }
        if min_index != i {
            arr.swap(i, min_index);
        }
        i = i + 1;
    }
    arr
}

/* helper modified by LLM (iteration 4): fixed syntax error in invariant by removing extra comma */
fn sort_descending_vec(mut arr: Vec<i8>) -> (result: Vec<i8>)
    ensures
        result@.map(|i: int, x: i8| x as int).to_multiset() == old(&mut arr)@.map(|i: int, x: i8| x as int).to_multiset(),
        is_descending_sorted(result@.map(|i: int, x: i8| x as int))
{
    let n = arr.len();
    let mut i = 0;
    while i < n - 1
        invariant
            0 <= i as int <= n as int - 1,
            arr@.map(|j: int, x: i8| x as int).to_multiset() == old(&mut arr)@.map(|j: int, x: i8| x as int).to_multiset(),
            forall|j: int, k: int| 0 <= j < k < i as int ==> arr@[j as int] >= arr@[k as int],
            forall|j: int| i as int <= j < n as int ==> forall|k: int| 0 <= k < i as int ==> arr@[k as int] >= arr@[j as int]
        decreases n - i
    {
        let mut max_index = i;
        let mut j = i + 1;
        while j < n
            invariant
                i as int <= j as int <= n as int,
                i as int <= max_index as int < n as int,
                forall|k: int| i as int <= k < j as int ==> arr@[max_index as int] >= arr@[k as int]
            decreases n - j
        {
            if arr[j] > arr[max_index] {
                max_index = j;
            }
            j = j + 1;
        }
        if max_index != i {
            arr.swap(i, max_index);
        }
        i = i + 1;
    }
    arr
}
// </vc-helpers>


// <vc-spec>
fn sort_array(arr: Vec<i8>) -> (result: Vec<i8>)
    requires valid_input(arr@.map(|i: int, x: i8| x as int))
    ensures 
        result@.map(|i: int, x: i8| x as int).to_multiset() == arr@.map(|i: int, x: i8| x as int).to_multiset(),
        correctly_sorted(arr@.map(|i: int, x: i8| x as int), result@.map(|i: int, x: i8| x as int))
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): no changes needed, helper already fixed */
    let n = arr.len();
    if n == 0 {
        return Vec::new();
    }
    let first = arr[0];
    let last = arr[n-1];
    let do_ascending = n > 1 && (first + last) % 2 == 1;
    let do_descending = n > 1 && (first + last) % 2 == 0;

    if do_ascending {
        sort_ascending_vec(arr)
    } else if do_descending {
        sort_descending_vec(arr)
    } else {
        arr
    }
}
// </vc-code>


}

fn main() {}