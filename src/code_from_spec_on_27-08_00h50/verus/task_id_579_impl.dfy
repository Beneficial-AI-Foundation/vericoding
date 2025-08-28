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
    let mut index = 0;
    while index < arr.len()
        // invariants-start
        invariant
            0 <= index <= arr.len(),
            forall|m: int| 0 <= m < index ==> (arr[m] != key),
        decreases arr.len() - index,
        // invariants-end
    {
        if (arr[index] == key) {
            return true;
        }
        index += 1;
    }
    false
    // impl-end
}

proof fn lemma_vec_push<T>(vec: Seq<T>, i: T, l: usize)
    // pre-conditions-start
    requires
        l == vec.len(),
    // pre-conditions-end
    // post-conditions-start
    ensures
        forall|k: int| 0 <= k < vec.len() ==> #[trigger] vec[k] == vec.push(i)[k],
        vec.push(i).index(l as int) == i,
    // post-conditions-end
{
    // impl-start
    // impl-end
}

spec fn seq_contains_no_duplicates<T>(s: Seq<T>) -> bool {
    forall|i: int, j: int| 0 <= i < j < s.len() ==> s[i] != s[j]
}

proof fn lemma_push_preserves_no_duplicates(s: Seq<i32>, x: i32)
    requires
        seq_contains_no_duplicates(s),
        !s.contains(x),
    ensures
        seq_contains_no_duplicates(s.push(x)),
{
    let s_new = s.push(x);
    assert forall|i: int, j: int| 0 <= i < j < s_new.len() implies s_new[i] != s_new[j] by {
        if j < s.len() {
            assert(s_new[i] == s[i]);
            assert(s_new[j] == s[j]);
        } else if j == s.len() {
            assert(s_new[j] == x);
            if i < s.len() {
                assert(s_new[i] == s[i]);
                assert(s.contains(s[i]));
            }
        }
    }
}

proof fn lemma_vec_seq_correspondence(v: &Vec<i32>, s: Seq<i32>)
    requires
        s == v@,
    ensures
        forall|i: int| 0 <= i < v.len() ==> s.contains(v[i]),
{
}
// pure-end
// </vc-helpers>

// <vc-spec>
fn find_dissimilar(arr1: &Vec<i32>, arr2: &Vec<i32>) -> (result: Vec<i32>)
    // post-conditions-start
    ensures
        forall|i: int|
            0 <= i < arr1.len() ==> (!arr2@.contains(#[trigger] arr1[i]) ==> result@.contains(
                arr1[i],
            )),
        forall|i: int|
            0 <= i < arr2.len() ==> (!arr1@.contains(#[trigger] arr2[i]) ==> result@.contains(
                arr2[i],
            )),
        forall|i: int, j: int|
            0 <= i < j < result.len() ==> #[trigger] result[i] != #[trigger] result[j],
    // post-conditions-end
// </vc-spec>

// <vc-code>
{
    // impl-start
    let mut result = Vec::new();
    let mut i = 0;
    
    while i < arr1.len()
        invariant
            0 <= i <= arr1.len(),
            forall|k: int| 0 <= k < i ==> (!arr2@.contains(arr1[k]) ==> result@.contains(arr1[k])),
            forall|k: int, j: int| 0 <= k < j < result.len() ==> result[k] != result[j],
        decreases arr1.len() - i,
    {
        if !contains(arr2, arr1[i]) && !contains(&result, arr1[i]) {
            proof {
                lemma_push_preserves_no_duplicates(result@, arr1[i as int]);
            }
            result.push(arr1[i]);
        }
        i += 1;
    }
    
    let mut j = 0;
    while j < arr2.len()
        invariant
            0 <= j <= arr2.len(),
            forall|k: int| 0 <= k < arr1.len() ==> (!arr2@.contains(arr1[k]) ==> result@.contains(arr1[k])),
            forall|k: int| 0 <= k < j ==> (!arr1@.contains(arr2[k]) ==> result@.contains(arr2[k])),
            forall|k: int, l: int| 0 <= k < l < result.len() ==> result[k] != result[l],
        decreases arr2.len() - j,
    {
        if !contains(arr1, arr2[j]) && !contains(&result, arr2[j]) {
            proof {
                lemma_push_preserves_no_duplicates(result@, arr2[j as int]);
            }
            result.push(arr2[j]);
        }
        j += 1;
    }
    
    result
    // impl-end
}
// </vc-code>

} // verus!

fn main() {}