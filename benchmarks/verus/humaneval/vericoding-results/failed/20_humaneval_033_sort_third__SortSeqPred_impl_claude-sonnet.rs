// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): added comprehensive invariant checking and sorting logic helpers */
fn valid_index(i: usize, len: usize) -> bool {
    i < len
}

fn partially_sorted_up_to(sorted: Seq<i8>, p: Seq<bool>, up_to: int) -> bool {
    forall|i: int, j: int| 0 <= i < j < up_to && i < p.len() && j < p.len() && p[i] && p[j] ==> sorted[i] as int <= sorted[j] as int
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
    /* code modified by LLM (iteration 5): fixed bounds checking and added proper loop invariants for sorting */
    let mut sorted = s.clone();
    let n = sorted.len();
    
    for i in 0..n
        invariant
            sorted.len() == s.len(),
            s@.to_multiset() == sorted@.to_multiset(),
            forall|k: int| 0 <= k < s.len() && !p@[k] ==> sorted@[k] == s@[k],
            forall|x: int, y: int| 0 <= x < y < i && p@[x] && p@[y] ==> sorted@[x] as int <= sorted@[y] as int,
    {
        if i < p.len() && p[i] {
            for j in (i + 1)..n
                invariant
                    sorted.len() == s.len(),
                    s@.to_multiset() == sorted@.to_multiset(),
                    forall|k: int| 0 <= k < s.len() && !p@[k] ==> sorted@[k] == s@[k],
                    forall|x: int, y: int| 0 <= x < y < i && p@[x] && p@[y] ==> sorted@[x] as int <= sorted@[y] as int,
                    forall|k: int| i < k < j && p@[k] ==> sorted@[i] as int <= sorted@[k] as int,
            {
                if j < p.len() && p[j] && sorted[i] > sorted[j] {
                    let temp = sorted[i];
                    sorted.set(i, sorted[j]);
                    sorted.set(j, temp);
                }
            }
        }
    }
    
    sorted
}
// </vc-code>


}

fn main() {}