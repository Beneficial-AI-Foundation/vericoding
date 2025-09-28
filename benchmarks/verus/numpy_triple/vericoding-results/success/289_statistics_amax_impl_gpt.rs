// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): basic transitivity from k < i and i <= n implies k < n */
proof fn lt_trans(k: int, i: int, n: int)
    requires
        0 <= k,
        k < i,
        i <= n,
    ensures
        0 <= k,
        k < n,
{
    assert(k < n);
}
// </vc-helpers>

// <vc-spec>
fn amax(a: Vec<i8>) -> (result: i8)
    requires a.len() > 0,
    ensures
        (exists|max_idx: int| 0 <= max_idx < a.len() &&
            result as int == a@[max_idx] as int &&
            (forall|i: int| 0 <= i < a.len() ==> a@[i] as int <= result as int)) &&
        (exists|first_max_idx: int| 0 <= first_max_idx < a.len() &&
            result as int == a@[first_max_idx] as int &&
            (forall|i: int| 0 <= i < a.len() && a@[i] as int == result as int ==> first_max_idx <= i) &&
            (forall|i: int| 0 <= i < a.len() ==> a@[i] as int <= result as int)) &&
        ((forall|i: int, j: int| 0 <= i < a.len() && 0 <= j < a.len() ==> a@[i] as int == a@[j] as int) ==> 
            result as int == a@[0] as int) &&
        (exists|witness: int| 0 <= witness < a.len() && result as int == a@[witness] as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): fix invariants to avoid casting issues and ensure first-maximum semantics */
    let n: usize = a.len();
    let mut best_idx: usize = 0usize;
    let mut best: i8 = a[0];
    let mut i: usize = 1usize;

    while i < n
        invariant
            n == a.len(),
            0 < i,
            i <= n,
            best as int == a@[best_idx as int] as int,
            best_idx < i,
            (forall|k: int| 0 <= k < i as int ==> a@[k] as int <= best as int),
            (forall|k: int| 0 <= k < i as int && a@[k] as int == best as int ==> best_idx as int <= k),
        decreases (n as int) - (i as int)
    {
        let v: i8 = a[i];
        if v > best {
            best = v;
            best_idx = i;
        }
        i = i + 1;
    }

    best
}
// </vc-code>

}
fn main() {}