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
/* helper modified by LLM (iteration 5): Fixed ghost code usage and proper proof function implementation */

proof fn sort_ascending_ensures_multiset(arr: Seq<int>) -> (result: Seq<int>)
    ensures
        result.to_multiset() == arr.to_multiset(),
        is_ascending_sorted(result)
    decreases arr.len()
{
    if arr.len() <= 1 {
        arr
    } else {
        let mid: int = arr.len() / 2;
        let left = sort_ascending_ensures_multiset(arr.subrange(0, mid));
        let right = sort_ascending_ensures_multiset(arr.subrange(mid, arr.len()));
        merge_ascending(left, right)
    }
}

proof fn sort_descending_ensures_multiset(arr: Seq<int>) -> (result: Seq<int>)
    ensures
        result.to_multiset() == arr.to_multiset(),
        is_descending_sorted(result)
    decreases arr.len()
{
    if arr.len() <= 1 {
        arr
    } else {
        let mid: int = arr.len() / 2;
        let left = sort_descending_ensures_multiset(arr.subrange(0, mid));
        let right = sort_descending_ensures_multiset(arr.subrange(mid, arr.len()));
        merge_descending(left, right)
    }
}

proof fn merge_ascending(left: Seq<int>, right: Seq<int>) -> (result: Seq<int>)
    ensures
        result.to_multiset() == left.to_multiset().add(right.to_multiset()),
        is_ascending_sorted(result)
    decreases left.len() + right.len()
{
    if left.len() == 0 {
        right
    } else if right.len() == 0 {
        left
    } else if left[0] <= right[0] {
        Seq::new(1, |i: int| left[0]) + merge_ascending(left.subrange(1, left.len()), right)
    } else {
        Seq::new(1, |i: int| right[0]) + merge_ascending(left, right.subrange(1, right.len()))
    }
}

proof fn merge_descending(left: Seq<int>, right: Seq<int>) -> (result: Seq<int>)
    ensures
        result.to_multiset() == left.to_multiset().add(right.to_multiset()),
        is_descending_sorted(result)
    decreases left.len() + right.len()
{
    if left.len() == 0 {
        right
    } else if right.len() == 0 {
        left
    } else if left[0] >= right[0] {
        Seq::new(1, |i: int| left[0]) + merge_descending(left.subrange(1, left.len()), right)
    } else {
        Seq::new(1, |i: int| right[0]) + merge_descending(left, right.subrange(1, right.len()))
    }
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
/* code modified by LLM (iteration 5): Fixed ghost code usage by moving sequence conversion to proof block */
    if arr.len() <= 1 {
        arr
    } else {
        let result_seq: Seq<int>;
        proof {
            let arr_seq = arr@.map(|i: int, x: i8| x as int);
            if should_sort_ascending(arr_seq) {
                result_seq = sort_ascending_ensures_multiset(arr_seq);
            } else {
                result_seq = sort_descending_ensures_multiset(arr_seq);
            }
            assert(correctly_sorted(arr_seq, result_seq));
            assert(result_seq.to_multiset() == arr_seq.to_multiset());
        }
        let mut result_vec = Vec::with_capacity(result_seq.len() as usize);
        for i in 0..result_seq.len() {
            result_vec.push(result_seq[i] as i8);
        }
        result_vec
    }
}
// </vc-code>


}

fn main() {}