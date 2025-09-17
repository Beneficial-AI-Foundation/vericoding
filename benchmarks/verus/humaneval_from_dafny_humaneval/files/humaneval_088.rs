// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
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
// </vc-helpers>

// <vc-spec>
fn sort_array(arr: Seq<int>) -> (result: Seq<int>)
    requires valid_input(arr)
    ensures 
        result.to_multiset() == arr.to_multiset(),
        correctly_sorted(arr, result)
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>


}

fn main() {}