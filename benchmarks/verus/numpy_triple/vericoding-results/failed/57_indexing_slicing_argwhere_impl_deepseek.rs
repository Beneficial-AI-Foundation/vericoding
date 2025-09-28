// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>


proof fn lemma_vec_index_unique_ordering(v: Vec<usize>)
    requires
        forall|i: int, j: int| 0 <= i < v@.len() && 0 <= j < v@.len() && i < j ==> v@[i] <= v@[j],
        forall|i: int, j: int| 0 <= i < v@.len() && 0 <= j < v@.len() && i != j ==> v@[i] != v@[j],
    ensures
        forall|i: int, j: int| 0 <= i < v@.len() && 0 <= j < v@.len() && i < j ==> v@[i] < v@[j],
{
    assert forall|i: int, j: int| 0 <= i < v@.len() && 0 <= j < v@.len() && i < j implies v@[i] < v@[j] by {
        assert(v@[i] <= v@[j]);
        assert(v@[i] != v@[j]);
    };
}

proof fn lemma_no_duplicates_imp_injective(v: Vec<usize>)
    requires
        forall|i: int, j: int| 0 <= i < v@.len() && 0 <= j < v@.len() && i != j ==> v@[i] != v@[j],
    ensures
        forall|i: int, j: int| 0 <= i < v@.len() && 0 <= j < v@.len() ==> (#[trigger] v@[i] == #[trigger] v@[j]) <==> i == j,
{
    assert forall|i: int, j: int| 0 <= i < v@.len() && 0 <= j < v@.len() implies (#[trigger] v@[i] == #[trigger] v@[j]) <==> i == j by {
        if v@[i] == v@[j] {
            if i != j {
                assert(false);
            }
            assert(i == j);
        } else {
            assert(i != j);
        }
    };
}

spec fn is_sorted(v: Seq<usize>) -> bool {
    forall|i: int, j: int| 0 <= i <= j < v.len() ==> v[i] <= v[j]
}

/* helper modified by LLM (iteration 5): fix type conversion in lemma_len_decreases */
proof fn lemma_len_decreases(i: usize, n: usize)
    requires
        i < n,
    ensures
        (n - i) as int < n as int,
{
    assert(n >= i + 1);
    assert(n as int - i as int >= 1);
    assert((n - i) as int > 0);
    assert(n as int - i as int == (n - i) as int);
    assert((n - i) as int <= n as int);
}


// </vc-helpers>

// <vc-spec>
fn argwhere(a: &Vec<f64>) -> (indices: Vec<usize>)
    ensures
        forall|i: int| 0 <= i < indices@.len() ==> (#[trigger] indices@[i] as int) < a@.len(),
        forall|i: int| 0 <= i < indices@.len() ==> a@[indices@[i] as int] != 0.0,
        forall|i: int| 0 <= i < a@.len() && a@[i] != 0.0 ==> exists|j: int| 0 <= j < indices@.len() && indices@[j] as int == i,
        forall|i: int, j: int| 0 <= i < indices@.len() && 0 <= j < indices@.len() && i != j ==> indices@[i] != indices@[j],
        forall|i: int, j: int| 0 <= i < indices@.len() && 0 <= j < indices@.len() && (indices@[i] as int) < (indices@[j] as int) ==> i < j,
        (indices@.len() == 0) == (forall|i: int| 0 <= i < a@.len() ==> a@[i] == 0.0),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): fix decreases clause syntax and strengthen invariants */
{
    let mut indices = Vec::new();
    let mut i: usize = 0;
    let n = a.len();
    
    while i < n
        invariant
            0 <= i <= n,
            forall|k: int| 0 <= k < indices@.len() ==> (#[trigger] indices@[k] as int) < i,
            forall|k: int| 0 <= k < indices@.len() ==> a@[indices@[k] as int] != 0.0,
            forall|k: int| 0 <= k < i && a@[k] != 0.0 ==> exists|j: int| 0 <= j < indices@.len() && indices@[j] as int == k,
            forall|k: int, l: int| 0 <= k < indices@.len() && 0 <= l < indices@.len() && k != l ==> indices@[k] != indices@[l],
            forall|k: int, l: int| 0 <= k < indices@.len() && 0 <= l < indices@.len() && k < l ==> (indices@[k] as int) < (indices@[l] as int),
        decreases n - i
    {
        lemma_len_decreases(i, n);
        if a[i] != 0.0 {
            indices.push(i);
        }
        i += 1;
    }
    
    proof {
        if indices@.len() == 0 {
            assert forall|k: int| 0 <= k < a@.len() implies a@[k] == 0.0 by {
                if a@[k] != 0.0 {
                    assert(exists|j: int| 0 <= j < indices@.len() && indices@[j] as int == k);
                    assert(false);
                }
            };
        } else {
            assert(exists|k: int| 0 <= k < a@.len() && a@[k] != 0.0);
        }
    }
    
    indices
}
// </vc-code>

}
fn main() {}