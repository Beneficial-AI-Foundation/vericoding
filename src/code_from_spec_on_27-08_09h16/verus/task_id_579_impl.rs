use vstd::prelude::*;

verus! {

// <vc-helpers>
fn contains(arr: &Vec<i32>, key: i32) -> (result: bool)
    ensures
        result == (exists|i: int| 0 <= i < arr.len() && (arr[i] == key)),
{
    let mut index = 0;
    while index < arr.len()
        invariant
            forall|m: int| 0 <= m < index ==> (arr[m] != key),
        decreases arr.len() - index,
    {
        if (arr[index] == key) {
            return true;
        }
        index += 1;
    }
    false
}

proof fn lemma_vec_push<T>(vec: Seq<T>, i: T, l: usize)
    requires
        l == vec.len(),
    ensures
        forall|k: int| 0 <= k < vec.len() ==> #[trigger] vec[k] == vec.push(i)[k],
        vec.push(i).index(l as int) == i,
{
}

proof fn lemma_result_contains_unique<T>(result: &Vec<T>, val: T)
    requires
        forall|i: int, j: int| 0 <= i < j < result.len() ==> #[trigger] result[i] != #[trigger] result[j],
        result@.contains(val),
    ensures
        exists|idx: int| 0 <= idx < result.len() && result[idx] == val,
{
}

proof fn lemma_contains_after_push<T>(vec: &Vec<T>, val: T)
    ensures
        (vec@.push(val)).contains(val),
{
    let new_seq = vec@.push(val);
    assert(new_seq.len() == vec@.len() + 1);
    assert(new_seq[vec@.len() as int] == val);
    assert(exists|i: int| 0 <= i < new_seq.len() && new_seq[i] == val);
}

proof fn lemma_uniqueness_preserved<T>(vec: &Vec<T>, val: T)
    requires
        forall|i: int, j: int| 0 <= i < j < vec.len() ==> #[trigger] vec[i] != #[trigger] vec[j],
        !vec@.contains(val),
    ensures
        forall|i: int, j: int| 0 <= i < j < (vec@.push(val)).len() ==> #[trigger] (vec@.push(val))[i] != #[trigger] (vec@.push(val))[j],
{
    let new_seq = vec@.push(val);
    assert(new_seq.len() == vec@.len() + 1);
    assert(new_seq[vec@.len() as int] == val);
}

proof fn lemma_contains_preserved<T>(vec: &Vec<T>, val: T, existing: T)
    requires
        vec@.contains(existing),
    ensures
        (vec@.push(val)).contains(existing),
{
    let new_seq = vec@.push(val);
    assert(exists|i: int| 0 <= i < vec@.len() && vec@[i] == existing);
    assert(forall|i: int| #![auto] 0 <= i < vec@.len() ==> new_seq[i] == vec@[i]);
    assert(exists|i: int| 0 <= i < new_seq.len() && new_seq[i] == existing) by {
        let idx = choose|i: int| 0 <= i < vec@.len() && vec@[i] == existing;
        assert(new_seq[idx] == existing);
    };
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
            forall|k: int| 0 <= k < i ==> (!arr2@.contains(#[trigger] arr1[k]) ==> result@.contains(arr1[k])),
            forall|x: int, y: int| 0 <= x < y < result.len() ==> #[trigger] result[x] != #[trigger] result[y],
        decreases arr1.len() - i,
    {
        let val = arr1[i];
        if !contains(arr2, val) && !contains(&result, val) {
            proof {
                lemma_uniqueness_preserved(&result, val);
                // Prove that adding val to result maintains all existing elements
                assert(forall|existing: i32| result@.contains(existing) ==> (result@.push(val)).contains(existing)) by {
                    forall|existing: i32| result@.contains(existing) implies (result@.push(val)).contains(existing) {
                        lemma_contains_preserved(&result, val, existing);
                    }
                };
            }
            result.push(val);
        }
        i += 1;
    }
    
    let mut j = 0;
    while j < arr2.len()
        invariant
            forall|k: int| 0 <= k < arr1.len() ==> (!arr2@.contains(#[trigger] arr1[k]) ==> result@.contains(arr1[k])),
            forall|k: int| 0 <= k < j ==> (!arr1@.contains(#[trigger] arr2[k]) ==> result@.contains(arr2[k])),
            forall|x: int, y: int| 0 <= x < y < result.len() ==> #[trigger] result[x] != #[trigger] result[y],
        decreases arr2.len() - j,
    {
        let val = arr2[j];
        if !contains(arr1, val) && !contains(&result, val) {
            proof {
                lemma_uniqueness_preserved(&result, val);
                // Prove that adding val to result maintains all existing elements
                assert(forall|existing: i32| result@.contains(existing) ==> (result@.push(val)).contains(existing)) by {
                    forall|existing: i32| result@.contains(existing) implies (result@.push(val)).contains(existing) {
                        lemma_contains_preserved(&result, val, existing);
                    }
                };
            }
            result.push(val);
        }
        j += 1;
    }
    
    result
}
// </vc-code>

} // verus!

fn main() {}