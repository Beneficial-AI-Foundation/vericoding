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
/* helper modified by LLM (iteration 5): Helper to convert sequence of ints back to Vec<i8> */
fn int_seq_to_vec(s: Seq<int>) -> (result: Vec<i8>)
    requires forall|i: int| 0 <= i < s.len() ==> 0 <= s[i] <= 127
    ensures result@ == s.map(|i: int, x: int| x as i8)
{
    let mut result = Vec::new();
    let mut i = 0;
    while i < s.len()
        invariant
            i <= s.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result@[j] == s[j] as i8
    {
        result.push(s[i] as i8);
        i += 1;
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
    /* code modified by LLM (iteration 5): Fixed Verus type casting by using usize for indexing */
    if arr.len() <= 1 {
        return arr;
    }
    
    let first = arr[0];
    let last = arr[arr.len() - 1];
    let sum = first + last;
    
    let ghost int_arr = arr@.map(|i: int, x: i8| x as int);
    
    if sum % 2 == 1 {
        proof {
            assert(should_sort_ascending(int_arr));
        }
        let ghost sorted_int = sort_ascending(int_arr);
        let mut result = Vec::new();
        let mut i = 0;
        while i < arr.len()
            invariant
                i <= arr.len(),
                result.len() == i,
                sorted_int.to_multiset() == int_arr.to_multiset(),
                is_ascending_sorted(sorted_int)
        {
            proof {
                assert(0 <= sorted_int[i as int] <= 127);
            }
            result.push(sorted_int[i] as i8);
            i += 1;
        }
        result
    } else {
        proof {
            assert(should_sort_descending(int_arr));
        }
        let ghost sorted_int = sort_descending(int_arr);
        let mut result = Vec::new();
        let mut i = 0;
        while i < arr.len()
            invariant
                i <= arr.len(),
                result.len() == i,
                sorted_int.to_multiset() == int_arr.to_multiset(),
                is_descending_sorted(sorted_int)
        {
            proof {
                assert(0 <= sorted_int[i as int] <= 127);
            }
            result.push(sorted_int[i] as i8);
            i += 1;
        }
        result
    }
}
// </vc-code>


}

fn main() {}