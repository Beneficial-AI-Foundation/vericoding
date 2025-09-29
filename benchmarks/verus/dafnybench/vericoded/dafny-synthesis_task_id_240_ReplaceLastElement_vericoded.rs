use vstd::prelude::*;

verus! {

// <vc-helpers>
fn append_vectors<T: Copy>(v1: &Vec<T>, v2: &Vec<T>) -> (result: Vec<T>)
    ensures
        result.len() == v1.len() + v2.len(),
        forall|i: int| 0 <= i && i < v1.len() ==> result[i] == v1[i],
        forall|i: int| v1.len() <= i && i < result.len() ==> result[i] == v2[i - v1.len()],
{
    let mut result = Vec::new();
    let mut i = 0;
    while i < v1.len()
        invariant
            i <= v1.len(),
            result.len() == i,
            forall|j: int| 0 <= j && j < i ==> result[j] == v1[j],
        decreases v1.len() - i
    {
        result.push(v1[i]);
        i += 1;
    }

    let mut j = 0;
    while j < v2.len()
        invariant
            j <= v2.len(),
            result.len() == v1.len() + j,
            forall|k: int| 0 <= k && k < v1.len() ==> result[k] == v1[k],
            forall|k: int| v1.len() <= k && k < v1.len() + j ==> result[k] == v2[k - v1.len()],
        decreases v2.len() - j
    {
        result.push(v2[j]);
        j += 1;
    }
    result
}
// </vc-helpers>

// <vc-spec>
fn replace_last_element(first: &Vec<i32>, second: &Vec<i32>) -> (result: Vec<i32>)
    requires 
        first.len() > 0,
    ensures 
        result.len() == first.len() - 1 + second.len(),
        forall|i: int| 0 <= i < first.len() - 1 ==> result[i] == first[i],
        forall|i: int| first.len() - 1 <= i < result.len() ==> result[i] == second[i - first.len() + 1],
// </vc-spec>
// <vc-code>
{
    let mut prefix_vec = Vec::new();
    let mut i = 0;
    while i < first.len() - 1
        invariant
            i <= first.len() - 1,
            prefix_vec.len() == i,
            forall|j: int| 0 <= j && j < i ==> prefix_vec[j] == first[j],
        decreases (first.len() - 1) - i
    {
        prefix_vec.push(first[i]);
        i += 1;
    }

    let result = append_vectors(&prefix_vec, second);

    assert(result.len() == (first.len() - 1) + second.len());

    assert(forall|k: int| 0 <= k && k < first.len() - 1 ==> result[k] == first[k]); {
        if first.len() - 1 > 0 { // Only apply if first.len() - 1 is positive
            assert(forall|k: int| 0 <= k && k < prefix_vec.len() ==> result[k] == prefix_vec[k]);
            assert(forall|k: int| 0 <= k && k < prefix_vec.len() ==> prefix_vec[k] == first[k]);
            assert(forall|i: int| 0 <= i && i < first.len() -1 ==> result[i] == first[i]);
        }
    }
    
    assert(forall|k: int| first.len() - 1 <= k && k < result.len() ==> result[k] == second[k - first.len() + 1]); {
        assert(first.len() - 1 == prefix_vec.len());
        assert(forall|k: int| prefix_vec.len() <= k && k < result.len() ==> result[k] == second[k - prefix_vec.len()]);
        
        // Let m = first.len() - 1. We need to show:
        // forall|k: int| m <= k < result.len() ==> result[k] == second[k - m]
        // Which is exactly what append_vectors ensures with prefix_vec.len() as m.
    }

    result
}
// </vc-code>

fn main() {
}

}