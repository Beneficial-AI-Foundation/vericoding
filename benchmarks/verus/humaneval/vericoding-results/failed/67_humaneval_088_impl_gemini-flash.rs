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
    /* code modified by LLM (iteration 5): Fixed compilation errors related to type mismatches and indexing sequence elements. Specifically, corrected `s_arr.len() <= 1` involving `nat`, used `result_seq.index(i)` for sequence indexing, and adjusted loop condition `i < result_seq.len()` for type compatibility. */
    let s_arr = arr@.map(|i: int, x: i8| x.into());

    let result_seq: Seq<int>;

    if (s_arr.len() as int) <= 1 {
        result_seq = s_arr;
    } else if should_sort_ascending(s_arr) {
        result_seq = sort_ascending(s_arr);
    } else {
        result_seq = sort_descending(s_arr);
    }

    proof {
        assert(result_seq.to_multiset() == s_arr.to_multiset());
        assert(result_seq.len() == s_arr.len()) by { // This assertion is crucial for `result_seq.len() == s_arr.len()` in the invariant
            if (s_arr.len() as int) <= 1 {
                assert(result_seq.len() == s_arr.len());
            } else if should_sort_ascending(s_arr) {
                assert(result_seq.to_multiset().len() == s_arr.to_multiset().len());
                assert(result_seq.len() == s_arr.len());
            } else {
                assert(result_seq.to_multiset().len() == s_arr.to_multiset().len());
                assert(result_seq.len() == s_arr.len());
            }
        }
    }


    let mut result_vec = Vec::new();
    let mut i: nat = 0;
    while i < result_seq.len()
        invariant
            0 <= i as int <= result_seq.len() as int,
            result_vec@.len() == i,
            forall|j: int| 0 <= j < i ==> result_vec@[j] as int == result_seq.index(j),
            result_seq.len() == s_arr.len()
        decreases result_seq.len() - i
    {
        result_vec.push(result_seq.index(i) as i8);
        i = i + 1;
    }
    result_vec
}
// </vc-code>


}

fn main() {}