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
/* helper modified by LLM (iteration 5): Added decreases clauses to fix loop verification */
fn bubble_sort_ascending(arr: &Vec<i8>) -> (result: Vec<i8>)
    ensures
        result@.len() == arr@.len(),
        result@.map(|i: int, x: i8| x as int).to_multiset() == arr@.map(|i: int, x: i8| x as int).to_multiset(),
        is_ascending_sorted(result@.map(|i: int, x: i8| x as int))
{
    let mut result = arr.clone();
    let n = result.len();
    
    if n <= 1 {
        return result;
    }
    
    let mut i: usize = 0;
    while i < n - 1
        invariant
            result@.len() == arr@.len(),
            result@.map(|i: int, x: i8| x as int).to_multiset() == arr@.map(|i: int, x: i8| x as int).to_multiset(),
            i <= n - 1,
            n == result.len(),
            forall|k: int, l: int| 0 <= k <= i && i < l < n ==> result@[k] as int <= result@[l] as int,
            forall|k: int, l: int| 0 <= k < l <= i ==> result@[k] as int <= result@[l] as int,
        decreases n - 1 - i
    {
        let mut j: usize = i + 1;
        while j < n
            invariant
                result@.len() == arr@.len(),
                result@.map(|i: int, x: i8| x as int).to_multiset() == arr@.map(|i: int, x: i8| x as int).to_multiset(),
                i < j <= n,
                n == result.len(),
                forall|k: int| i < k < j ==> result@[i as int] as int <= result@[k] as int,
                forall|k: int, l: int| 0 <= k <= i && i < l < n ==> result@[k] as int <= result@[l] as int,
                forall|k: int, l: int| 0 <= k < l <= i ==> result@[k] as int <= result@[l] as int,
            decreases n - j
        {
            if result[i] > result[j] {
                let temp = result[i];
                result.set(i, result[j]);
                result.set(j, temp);
            }
            j = j + 1;
        }
        i = i + 1;
    }
    result
}

fn bubble_sort_descending(arr: &Vec<i8>) -> (result: Vec<i8>)
    ensures
        result@.len() == arr@.len(),
        result@.map(|i: int, x: i8| x as int).to_multiset() == arr@.map(|i: int, x: i8| x as int).to_multiset(),
        is_descending_sorted(result@.map(|i: int, x: i8| x as int))
{
    let mut result = arr.clone();
    let n = result.len();
    
    if n <= 1 {
        return result;
    }
    
    let mut i: usize = 0;
    while i < n - 1
        invariant
            result@.len() == arr@.len(),
            result@.map(|i: int, x: i8| x as int).to_multiset() == arr@.map(|i: int, x: i8| x as int).to_multiset(),
            i <= n - 1,
            n == result.len(),
            forall|k: int, l: int| 0 <= k <= i && i < l < n ==> result@[k] as int >= result@[l] as int,
            forall|k: int, l: int| 0 <= k < l <= i ==> result@[k] as int >= result@[l] as int,
        decreases n - 1 - i
    {
        let mut j: usize = i + 1;
        while j < n
            invariant
                result@.len() == arr@.len(),
                result@.map(|i: int, x: i8| x as int).to_multiset() == arr@.map(|i: int, x: i8| x as int).to_multiset(),
                i < j <= n,
                n == result.len(),
                forall|k: int| i < k < j ==> result@[i as int] as int >= result@[k] as int,
                forall|k: int, l: int| 0 <= k <= i && i < l < n ==> result@[k] as int >= result@[l] as int,
                forall|k: int, l: int| 0 <= k < l <= i ==> result@[k] as int >= result@[l] as int,
            decreases n - j
        {
            if result[i] < result[j] {
                let temp = result[i];
                result.set(i, result[j]);
                result.set(j, temp);
            }
            j = j + 1;
        }
        i = i + 1;
    }
    result
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
    /* code modified by LLM (iteration 5): No changes needed to main function body */
    if arr.len() <= 1 {
        return arr;
    }
    
    let first = arr[0] as i32;
    let last = arr[arr.len() - 1] as i32;
    
    if (first + last) % 2 == 1 {
        // Sort ascending
        bubble_sort_ascending(&arr)
    } else {
        // Sort descending  
        bubble_sort_descending(&arr)
    }
}
// </vc-code>


}

fn main() {}