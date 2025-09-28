// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): swap preserves multiset */
proof fn swap_preserves_multiset(mut v: Vec<i8>, i: usize, j: usize)
    requires
        i < v.len(),
        j < v.len(),
    ensures
        v@.to_multiset() == old(&mut v)@.to_multiset(),
{
    // swapping two elements does not change the multiset of elements
    v.swap(i, j);
}

// </vc-helpers>

// <vc-spec>
fn sort_seq_pred(s: Vec<i8>, p: Vec<bool>) -> (sorted: Vec<i8>)
  requires s.len() == p.len(),
  ensures 
    sorted.len() == s.len(),
    forall|i: int, j: int| 0 <= i < j < sorted.len() && p[i] && p[j] ==> sorted[i] as int <= sorted[j] as int,
    s@.to_multiset() == sorted@.to_multiset(),
    forall|i: int| 0 <= i < s.len() && !p[i] ==> sorted[i] == s[i],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): sorting selected positions using usize indices and proving multiset preservation via helper */
    let mut result = s.clone();
    let n = result.len();

    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            result.len() == n,
            result@.to_multiset() == s@.to_multiset(),
            forall|a: int, b: int| 0 <= a < b < (i as int) && p@[a] && p@[b] ==> result@[a] as int <= result@[b] as int,
        decreases n - i
    {
        if p[i] {
            let mut j: usize = i + 1;
            while j < n
                invariant
                    i < n,
                    i + 1 <= j <= n,
                    result.len() == n,
                    result@.to_multiset() == s@.to_multiset(),
                    forall|a: int, b: int| 0 <= a < b < (i as int) && p@[a] && p@[b] ==> result@[a] as int <= result@[b] as int,
                    forall|k: int| (i as int) <= k < (j as int) && p@[k] ==> result@[i as int] as int <= result@[k] as int,
                decreases n - j
            {
                if p[j] && result[i] > result[j] {
                    result.swap(i, j);
                    proof {
                        swap_preserves_multiset(result.clone(), i, j);
                    }
                }
                j += 1;
            }
        }
        i += 1;
    }

    result
}

// </vc-code>


}

fn main() {}