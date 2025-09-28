use vstd::prelude::*;

verus! {

fn swap(arr: &mut Vec<i32>, i: usize, j: usize)
    requires 
        old(arr).len() > 0,
        i < old(arr).len(),
        j < old(arr).len(),
    ensures
        arr[i as int] == old(arr)[j as int],
        arr[j as int] == old(arr)[i as int],
        forall|k: int| 0 <= k < arr.len() && k != i && k != j ==> arr[k] == old(arr)[k],
        arr@.to_multiset() == old(arr)@.to_multiset(),
{
    assume(false);
}

spec fn count(arr: Seq<i32>, value: i32) -> nat
    decreases arr.len(),
{
    if arr.len() == 0 {
        0nat
    } else {
        (if arr[0] == value { 1nat } else { 0nat }) + count(arr.skip(1), value)
    }
}

proof fn count_bound(arr: Seq<i32>, value: i32)
    ensures count(arr, value) <= arr.len(),
    decreases arr.len(),
{
    if arr.len() == 0 {
    } else {
        count_bound(arr.skip(1), value);
    }
}

// <vc-helpers>
spec fn is_permutation(arr1: Seq<i32>, arr2: Seq<i32>) -> bool {
    arr1.to_multiset() == arr2.to_multiset()
}

proof fn permutation_is_reflexive(arr: Seq<i32>)
    ensures is_permutation(arr, arr),
{
    assert(arr.to_multiset() == arr.to_multiset());
}

proof fn permutation_is_symmetric(arr1: Seq<i32>, arr2: Seq<i32>)
    requires is_permutation(arr1, arr2)
    ensures is_permutation(arr2, arr1),
{
    assert(arr1.to_multiset() == arr2.to_multiset());
}

proof fn permutation_is_transitive(arr1: Seq<i32>, arr2: Seq<i32>, arr3: Seq<i32>)
    requires is_permutation(arr1, arr2) && is_permutation(arr2, arr3)
    ensures is_permutation(arr1, arr3),
{
    assert(arr1.to_multiset() == arr2.to_multiset() && arr2.to_multiset() == arr3.to_multiset());
}

proof fn swap_preserves_permutation(arr: &mut Vec<i32>, i: usize, j: usize)
    requires
        old(arr).len() > 0,
        i < old(arr).len(),
        j < old(arr).len(),
    ensures
        is_permutation(old(arr)@, arr@),
{
    assert(arr@.to_multiset() == old(arr)@.to_multiset());
}

proof fn lemma_count_add_element(arr: Seq<i32>, value: i32, c: i32)
    ensures count(arr.push(c), value) 
        == (if c == value { 1nat } else { 0nat }) + count(arr, value),
    decreases arr.len(),
{
    if arr.len() == 0 {
        assert(count(Seq::empty().push(c), value) == (if c == value { 1nat } else { 0nat }) + count(Seq::empty(), value));
    } else {
        lemma_count_add_element(arr.skip(1), value, c);
        assert(count(arr.push(c), value) == count(arr.skip(1).push(c), value) + (if arr[0] == value { 1nat } else { 0nat }));
    }
}

proof fn lemma_count_remove_element(arr: Seq<i32>, value: i32)
    requires arr.len() > 0
    ensures count(arr, value) 
        == (if arr[0] == value { 1nat } else { 0nat }) + count(arr.skip(1), value),
    decreases arr.len(),
{
    if arr.len() == 1 {
    } else {
        lemma_count_remove_element(arr.skip(1), value);
    }
}
// </vc-helpers>

// <vc-spec>
fn move_zeros_to_end(arr: &mut Vec<i32>)
    requires old(arr).len() >= 2,
    ensures
        // Same size
        arr.len() == old(arr).len(),
        // Zeros to the right of the first zero
        forall|i: int, j: int| 0 <= i < j < arr.len() && arr[i] == 0 ==> arr[j] == 0,
        // The final array is a permutation of the original one
        arr@.to_multiset() == old(arr)@.to_multiset(),
        // Relative order of non-zero elements is preserved
        forall|n: int, m: int| 0 <= n < m < arr.len() && old(arr)[n] != 0 && old(arr)[m] != 0 ==>
            exists|k: int, l: int| 0 <= k < l < arr.len() && arr[k] == old(arr)[n] && arr[l] == old(arr)[m],
        // Number of zeros is preserved
// </vc-spec>
// <vc-code>
{
    let n = arr.len();
    let mut i = 0;
    let mut j = n - 1;
    
    while i < j
        invariant
            0 <= i <= j + 1 <= n,
            forall|k: int| 0 <= k < i ==> arr[k] != 0,
            forall|k: int| j < k < n ==> arr[k] == 0,
            arr@.to_multiset() == old(arr)@.to_multiset(),
            forall|n: int, m: int| 0 <= n < m < n && old(arr)[n] != 0 && old(arr)[m] != 0 ==>
                ((arr.index_of(old(arr)[n]) as int) < (arr.index_of(old(arr)[m]) as int)),
    {
        if arr[i] == 0 {
            if arr[j] != 0 {
                arr.swap(i, j);
                proof {
                    swap_preserves_permutation(arr, i, j);
                }
                i = i + 1;
            };
            j = j - 1;
        } else {
            i = i + 1;
        }
    }
}
// </vc-code>

fn main() {}

}