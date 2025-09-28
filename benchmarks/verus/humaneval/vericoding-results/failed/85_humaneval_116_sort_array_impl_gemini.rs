// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn popcount(n: nat) -> nat
    decreases n
{
    if n == 0 { 0 } else { popcount(n / 2) + n % 2 }
}
// </vc-preamble>

// <vc-helpers>
spec fn is_sorted_by_popcount(s: Seq<u8>) -> bool {
    forall|i: int, j: int| 0 <= i < j < s.len() ==> popcount(s[i] as nat) <= popcount(s[j] as nat)
}

fn exec_popcount(n: u8) -> (count: u8)
    ensures
        count as nat == popcount(n as nat),
{
    let mut temp_n = n;
    let mut cnt: u8 = 0;
    while temp_n > 0
        invariant
            popcount(n as nat) == popcount(temp_n as nat) + cnt as nat,
            cnt <= 8,
    {
        proof {
            assert(popcount(temp_n as nat) == popcount((temp_n / 2) as nat) + temp_n % 2 as nat);
        }
        if temp_n % 2 == 1 {
            cnt = cnt + 1;
        }
        temp_n = temp_n / 2;
    }
    cnt
}
// </vc-helpers>

// <vc-spec>
fn sort_array(s: Vec<u8>) -> (sorted: Vec<u8>)
    ensures 
        forall|i: int, j: int| 0 <= i < j < sorted@.len() ==> popcount(sorted@[i] as nat) <= popcount(sorted@[j] as nat)
            && sorted@.len() == s@.len()
            && s@.to_multiset() == sorted@.to_multiset()
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed incorrect path for lemma_swap_preserves_multiset */
    let mut sorted = s;
    let len = sorted.len();
    let mut i: usize = 0;
    while i < len
        invariant
            0 <= i <= len,
            sorted.len() == len,
            s@.to_multiset() == sorted@.to_multiset(),
            is_sorted_by_popcount(sorted@.subrange(0, i as int)),
            forall|k1: int, k2: int|
                0 <= k1 < i && i <= k2 < len ==> popcount(sorted@[k1] as nat) <= popcount(sorted@[k2] as nat),
        decreases len - i
    {
        let mut min_idx = i;
        let mut j = i + 1;
        while j < len
            invariant
                i < j <= len,
                i <= min_idx,
                min_idx < j,
                forall|k: int| i <= k < j ==> popcount(sorted@[min_idx] as nat) <= popcount(sorted@[k] as nat),
            decreases len - j
        {
            if exec_popcount(sorted[j]) < exec_popcount(sorted[min_idx]) {
                min_idx = j;
            }
            j = j + 1;
        }

        proof {
            assert forall|k: int| i <= k < len implies popcount(sorted@[min_idx] as nat) <= popcount(sorted@[k] as nat) by {}
        }

        let ghost s_old = sorted@;
        sorted.swap(i, min_idx);
        proof {
            vstd::seq_lib::lemma_swap_preserves_multiset(s_old, i as int, min_idx as int);
        }
        
        i = i + 1;
    }
    sorted
}
// </vc-code>


}

fn main() {}