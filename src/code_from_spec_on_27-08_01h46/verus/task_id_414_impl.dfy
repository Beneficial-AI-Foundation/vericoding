use vstd::prelude::*;

verus! {

// <vc-helpers>
fn contains(arr: &Vec<i32>, key: i32) -> (result: bool)
    // post-conditions-start
    ensures
        result == (exists|i: int| 0 <= i < arr.len() && (arr[i] == key)),
    // post-conditions-end
{
    // impl-start
    let mut i = 0;
    while i < arr.len()
        // invariants-start
        invariant
            0 <= i <= arr.len(),
            forall|m: int| 0 <= m < i ==> (arr[m] != key),
        decreases arr.len() - i
        // invariants-end
    {
        if (arr[i] == key) {
            return true;
        }
        i += 1;
    }
    false
    // impl-end
}

proof fn lemma_seq_contains_equiv(seq: Seq<i32>, value: i32)
    ensures
        seq.contains(value) == exists|k: int| 0 <= k < seq.len() && seq[k] == value,
{
}
// </vc-helpers>

// <vc-spec>
fn any_value_exists(arr1: &Vec<i32>, arr2: &Vec<i32>) -> (result: bool)
    // post-conditions-start
    ensures
        result == exists|k: int| 0 <= k < arr1.len() && arr2@.contains(#[trigger] arr1[k]),
    // post-conditions-end
// </vc-spec>

// <vc-code>
{
    // impl-start
    let mut i = 0;
    while i < arr1.len()
        invariant
            0 <= i <= arr1.len(),
            forall|k: int| 0 <= k < i ==> !arr2@.contains(arr1[k]),
        decreases arr1.len() - i
    {
        proof {
            lemma_seq_contains_equiv(arr2@, arr1[i as int]);
        }
        if contains(arr2, arr1[i]) {
            return true;
        }
        i += 1;
    }
    false
    // impl-end
}
// </vc-code>

} // verus!

fn main() {}