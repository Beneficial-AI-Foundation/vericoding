use vstd::prelude::*;

verus! {

// <vc-helpers>
// Helper lemma to prove uniqueness is preserved when adding a new element
proof fn lemma_uniqueness_preserved(v: Seq<i32>, x: i32)
    requires
        forall|i: int, j: int| 0 <= i < j < v.len() ==> #[trigger] v[i] != #[trigger] v[j],
        !v.contains(x)
    ensures
        forall|i: int, j: int| 0 <= i < j < v.push(x).len() ==> #[trigger] v.push(x)[i] != #[trigger] v.push(x)[j]
{
    let new_v = v.push(x);
    assert forall|i: int, j: int| 0 <= i < j < new_v.len() implies #[trigger] new_v[i] != #[trigger] new_v[j] by {
        if j == new_v.len() - 1 {
            // j is the last element (x)
            assert(new_v[j] == x);
            assert(0 <= i < j);
            if i < v.len() {
                assert(new_v[i] == v[i]);
                assert(v.contains(v[i]));
                assert(new_v[i] != x);
            }
        } else {
            // Both i and j are from the original vector
            assert(i < v.len() && j < v.len());
            assert(new_v[i] == v[i]);
            assert(new_v[j] == v[j]);
            assert(v[i] != v[j]);
        }
    }
}
// </vc-helpers>

// <vc-spec>
fn remove_duplicates(a: &[i32]) -> (result: Vec<i32>)
    ensures
        forall|x: i32| result@.contains(x) <==> exists|i: int| 0 <= i < a.len() && a[i] == x,
        forall|i: int, j: int| 0 <= i < j < result.len() ==> result@[i] != result@[j]
// </vc-spec>
// <vc-code>
{
    let mut result = Vec::new();
    
    for i in 0..a.len()
        invariant
            forall|x: i32| result@.contains(x) <==> exists|k: int| 0 <= k < i && a[k] == x,
            forall|i: int, j: int| 0 <= i < j < result.len() ==> result@[i] != result@[j]
    {
        let current = a[i];
        
        if !result@.contains(current) {
            proof {
                lemma_uniqueness_preserved(result@, current);
            }
            result.push(current);
        }
        
        assert(exists|k: int| 0 <= k < (i as int) + 1 && a[k] == current) by {
            assert(0 <= i as int && (i as int) < (i as int) + 1 && a[i as int] == current);
        }
    }
    
    result
}
// </vc-code>

fn main() {
}

}