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

proof fn lemma_contains_after_push(v: Seq<i32>, elem: i32, new_elem: i32)
    ensures
        v.contains(elem) ==> v.push(new_elem).contains(elem),
        v.push(new_elem).contains(new_elem),
{
    assert forall|i: int| 0 <= i < v.len() implies v.push(new_elem)[i] == v[i] by {
        assert(v.push(new_elem)[i] == v[i]);
    }
    
    if v.contains(elem) {
        let k = choose|k: int| 0 <= k < v.len() && v[k] == elem;
        assert(v.push(new_elem)[k] == v[k]);
        assert(v.push(new_elem)[k] == elem);
        assert(v.push(new_elem).contains(elem));
    }
    
    let last_idx = v.len() as int;
    assert(v.push(new_elem)[last_idx] == new_elem);
    assert(v.push(new_elem).contains(new_elem));
}

proof fn lemma_unique_after_push(result: Seq<i32>, elem: i32)
    requires
        forall|i: int, j: int| 0 <= i < j < result.len() ==> result[i] != result[j],
        !result.contains(elem),
    ensures
        forall|i: int, j: int| 0 <= i < j < result.push(elem).len() ==> result.push(elem)[i] != result.push(elem)[j],
{
    let new_seq = result.push(elem);
    assert forall|i: int, j: int| 0 <= i < j < new_seq.len() implies new_seq[i] != new_seq[j] by {
        if i < result.len() && j < result.len() {
            assert(new_seq[i] == result[i]);
            assert(new_seq[j] == result[j]);
            assert(result[i] != result[j]);
        } else if i < result.len() && j == result.len() {
            assert(new_seq[i] == result[i]);
            assert(new_seq[j] == elem);
            assert(!result.contains(elem));
            assert(result[i] != elem);
        }
    }
}
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
    let mut result: Vec<i32> = Vec::new();
    
    let mut i = 0;
    while i < arr1.len()
        invariant
            0 <= i <= arr1.len(),
            forall|k: int| 0 <= k < i ==> (!arr2@.contains(arr1[k]) ==> result@.contains(arr1[k])),
            forall|k: int, j: int| 0 <= k < j < result.len() ==> result[k] != result[j],
        decreases arr1.len() - i,
    {
        if !contains(arr2, arr1[i])
        {
            if !contains(&result, arr1[i])
            {
                proof {
                    lemma_unique_after_push(result@, arr1[i as int]);
                }
                result.push(arr1[i]);
            }
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
        if !contains(arr1, arr2[j])
        {
            if !contains(&result, arr2[j])
            {
                let old_result = result@;
                proof {
                    lemma_unique_after_push(result@, arr2[j as int]);
                }
                result.push(arr2[j]);
                proof {
                    assert forall|k: int| 0 <= k < arr1.len() implies (!arr2@.contains(arr1[k]) ==> result@.contains(arr1[k])) by {
                        if !arr2@.contains(arr1[k]) {
                            if k < arr1.len() {
                                lemma_contains_after_push(old_result, arr1[k], arr2[j as int]);
                            }
                        }
                    }
                }
            }
        }
        j += 1;
    }
    
    result
}
// </vc-code>

} // verus!

fn main() {}