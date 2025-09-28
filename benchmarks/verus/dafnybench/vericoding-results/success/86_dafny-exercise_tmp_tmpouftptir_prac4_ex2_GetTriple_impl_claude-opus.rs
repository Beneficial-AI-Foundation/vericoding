use vstd::prelude::*;

verus! {

spec fn triple(a: &[int]) -> bool {
    exists|i: int| 0 <= i < a.len() - 2 && #[trigger] a[i] == a[i + 1] && a[i + 1] == a[i + 2]
}

// <vc-helpers>
// Helper lemma to establish that if we haven't found a triple up to index i,
// and there's no triple at i, then there's no triple in the range [0, i+1)
proof fn no_triple_extension(a: &[int], i: int)
    requires
        0 <= i < a.len() - 2,
        forall|j: int| 0 <= j < i ==> !(#[trigger] a[j] == a[j + 1] && a[j + 1] == a[j + 2]),
        !(a[i] == a[i + 1] && a[i + 1] == a[i + 2]),
    ensures
        forall|j: int| 0 <= j < i + 1 ==> !(#[trigger] a[j] == a[j + 1] && a[j + 1] == a[j + 2]),
{
}

// Helper lemma to connect the existence of a triple at a specific index to the spec
proof fn triple_at_index_implies_triple(a: &[int], index: int)
    requires
        0 <= index < a.len() - 2,
        a[index] == a[index + 1] && a[index + 1] == a[index + 2],
    ensures
        triple(a),
{
    assert(exists|i: int| 0 <= i < a.len() - 2 && #[trigger] a[i] == a[i + 1] && a[i + 1] == a[i + 2]);
}

// Helper lemma for when no triple exists up to the end
proof fn no_triple_up_to_end(a: &[int])
    requires
        forall|j: int| 0 <= j < a.len() - 2 ==> !(#[trigger] a[j] == a[j + 1] && a[j + 1] == a[j + 2]),
    ensures
        !triple(a),
{
}
// </vc-helpers>

// <vc-spec>
fn get_triple(a: &[int]) -> (index: usize)
ensures 
    (0 <= index < a.len() - 1) || index == a.len(),
    index == a.len() <==> !triple(a),
    (0 <= index < a.len() - 1) <==> triple(a),
    (0 <= index < a.len() - 1) ==> a[index as int] == a[index as int + 1] && a[index as int + 1] == a[index as int + 2]
// </vc-spec>
// <vc-code>
{
    if a.len() < 3 {
        // No room for a triple
        assert(!triple(a)) by {
            assert(forall|i: int| 0 <= i < a.len() - 2 ==> #[trigger] a[i] == a[i + 1] && a[i + 1] == a[i + 2] ==> false);
        }
        return a.len();
    }

    let mut i: usize = 0;
    
    while i < a.len() - 2
        invariant
            i <= a.len() - 2,
            forall|j: int| 0 <= j < i ==> !(#[trigger] a[j as int] == a[j + 1] && a[j + 1] == a[j + 2]),
        decreases a.len() - 2 - i,
    {
        if a[i] == a[i + 1] && a[i + 1] == a[i + 2] {
            proof {
                triple_at_index_implies_triple(a, i as int);
            }
            return i;
        }
        
        proof {
            no_triple_extension(a, i as int);
        }
        i = i + 1;
    }
    
    proof {
        no_triple_up_to_end(a);
    }
    a.len()
}
// </vc-code>

fn main() {}

}