// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): use old(v) in `requires` clause for &mut parameter */
fn swap(v: &mut Vec<i8>, i: usize, j: usize)
    requires
        (i as int) < old(v)@.len(),
        (j as int) < old(v)@.len(),
    ensures
        v@.len() == old(v)@.len(),
        v@.to_multiset() == old(v)@.to_multiset(),
        v@[i as int] == old(v)@[j as int],
        v@[j as int] == old(v)@[i as int],
        forall|k: int| 0 <= k < v@.len() && k != (i as int) && k != (j as int) ==> v@[k] == old(v)@[k],
{
    let temp = v[i];
    v.set(i, v[j]);
    v.set(j, temp);
}

/* helper modified by LLM (iteration 5): removed exists quantifiers causing trigger issues and added triggers */
fn find_min_idx(a: &Vec<i8>, start_idx: usize) -> (min_idx: usize)
    requires
        (start_idx as int) < a@.len(),
        start_idx % 2 == 0,
    ensures
        start_idx <= min_idx,
        (min_idx as int) < a@.len(),
        min_idx % 2 == 0,
        forall|k: int| (start_idx as int) <= k < a@.len() && k % 2 == 0 ==> #[trigger] a@[k] >= a@[min_idx as int],
{
    let mut min_idx = start_idx;
    let mut i = start_idx + 2;
    while i < a.len()
        invariant
            start_idx <= min_idx,
            (min_idx as int) < a@.len(),
            min_idx % 2 == 0,
            i % 2 == 0 || (i as int) == a@.len() || (i as int) == a@.len() + 1,
            start_idx < i,
            forall|k: int| (start_idx as int) <= k < (i as int) && k % 2 == 0 ==> #[trigger] a@[k] >= a@[min_idx as int],
        decreases a.len() - i
    {
        if a[i] < a[min_idx] {
            min_idx = i;
        }
        i = i + 2;
    }
    min_idx
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
    /* code modified by LLM (iteration 5): added triggers to loop invariants to prevent future errors */
    let mut result = a;
    let n = result.len();
    let mut i: usize = 0;
    while i < n
        invariant
            (n as int) == result@.len(),
            a@.len() == result@.len(),
            result@.to_multiset() == a@.to_multiset(),
            i % 2 == 0,
            i <= n,
            forall|k: int| 0 <= k < (n as int) && k % 2 == 1 ==> #[trigger] result@[k] == a@[k],
            forall|j: int, k: int| 0 <= j < k && 2 * k < (i as int) ==> #[trigger] result@[2*j] <= #[trigger] result@[2*k],
            forall|j: int, k: int| 0 <= 2*j < (i as int) && (i as int) <= 2*k && 2*k < (n as int) ==> #[trigger] result@[2*j] <= #[trigger] result@[2*k],
        decreases n - i
    {
        let min_idx = find_min_idx(&result, i);
        swap(&mut result, i, min_idx);
        i = i + 2;
    }
    result
}
// </vc-code>


}

fn main() {}