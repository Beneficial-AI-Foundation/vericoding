// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

proof fn sorted_even_lemma(a: Seq<i8>, i: int, j: int)
    requires
        0 <= i,
        i < j,
        2 * i < a.len(),
        2 * j < a.len(),
        forall|k: int, l: int| 0 <= k < l && 2 * k < a.len() && 2 * l < a.len() ==> #[trigger] a[2 * k] <= #[trigger] a[2 * l]
    ensures
        a[2 * i] <= a[2 * j]
{
    assert(a[2 * i] <= a[2 * j]);
}

fn swap_even_indices(a: &mut Vec<i8>, i: usize, j: usize)
    requires
        old(a)@.len() > 0,
        i < old(a)@.len() / 2,
        j < old(a)@.len() / 2,
        2 * i < old(a)@.len(),
        2 * j < old(a)@.len()
    ensures
        a@.len() == old(a)@.len(),
        forall|k: int| 0 <= k < a@.len() && k % 2 == 1 ==> a@[k] == old(a)@[k],
        a@.to_multiset() == old(a)@.to_multiset(),
        a@[2 * i] == old(a)@[2 * j],
        a@[2 * j] == old(a)@[2 * i],
        forall|k: int| 0 <= k < a@.len() && k != 2 * i && k != 2 * j ==> a@[k] == old(a)@[k]
{
    proof {
        assert(2 * i < old(a)@.len());
        assert(2 * j < old(a)@.len());
    }
    let temp = a[2 * i];
    a.set(2 * i, a[2 * j]);
    a.set(2 * j, temp);
}

// </vc-helpers>

// <vc-spec>
fn sorted_even(a: Vec<i8>) -> (sorted: Vec<i8>)
    requires 
        a@.len() > 0
    ensures 
        sorted@.len() == a@.len(),
        forall|i: int, j: int| 0 <= i < j && 2 * i < sorted@.len() && 2 * j < sorted@.len() ==> #[trigger] sorted@[2 * i] <= #[trigger] sorted@[2 * j],
        forall|i: int| 0 <= i < a@.len() && i % 2 == 1 ==> #[trigger] sorted@[i] == #[trigger] a@[i],
        a@.to_multiset() == sorted@.to_multiset()
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): Fixed quantified trigger annotation */
    let mut sorted = a.clone();
    let n = sorted.len();
    
    let mut outer: usize = 0;
    while outer < n / 2
        invariant
            outer <= n / 2,
            sorted@.len() == a@.len(),
            forall|k: int| 0 <= k < sorted@.len() && k % 2 == 1 ==> sorted@[k] == a@[k],
            sorted@.to_multiset() == a@.to_multiset()
        decreases (n / 2) - outer
    {
        let mut inner: usize = outer + 1;
        while inner < n / 2
            invariant
                outer < inner <= n / 2,
                sorted@.len() == a@.len(),
                forall|k: int| 0 <= k < sorted@.len() && k % 2 == 1 ==> sorted@[k] == a@[k],
                sorted@.to_multiset() == a@.to_multiset()
            decreases (n / 2) - inner
        {
            proof {
                assert(2 * outer < sorted@.len());
                assert(2 * inner < sorted@.len());
            }
            if sorted[2 * inner] < sorted[2 * outer] {
                swap_even_indices(&mut sorted, outer, inner);
            }
            inner += 1;
        }
        outer += 1;
    }
    
    proof {
        assert(forall|i: int, j: int| 0 <= i < j && 2 * i < sorted@.len() && 2 * j < sorted@.len() ==> #[trigger] sorted@[2 * i] <= #[trigger] sorted@[2 * j]);
    }
    sorted
}
// </vc-code>


}

fn main() {}