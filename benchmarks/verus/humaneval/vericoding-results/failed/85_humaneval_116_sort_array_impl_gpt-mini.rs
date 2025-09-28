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
/* helper modified by LLM (iteration 5): lemma relating spec popcount to u8.count_ones */
fn lemma_popcount_u8(nb: u8)
    ensures
        popcount(nb as nat) == (nb.count_ones() as nat),
    decreases
        nb as nat
{
    if nb == 0u8 {
        proof {
            assert(popcount(0 as nat) == 0);
            assert((0u8).count_ones() as nat == 0);
        }
    } else {
        proof {
            let nb2: u8 = nb >> 1;
            lemma_popcount_u8(nb2);
            assert(popcount(nb as nat) == popcount(nb2 as nat) + ((nb & 1u8) as nat));
            assert((nb.count_ones() as nat) == (nb2.count_ones() as nat) + ((nb & 1u8) as nat));
            assert(popcount(nb as nat) == (nb.count_ones() as nat));
        }
    }
}

/* helper modified by LLM (iteration 5): swap two elements in a Vec<u8> using usize indices */
fn swap_vec_u8(v: &mut Vec<u8>, i: usize, j: usize)
    requires
        i < v.len(),
        j < v.len(),
    ensures
        v@.to_multiset() == old(v)@.to_multiset(),
        v@.len() == old(v)@.len(),
{
    v.swap(i, j);
    proof {
        assert(v@.len() == old(v)@.len());
        assert(v@.to_multiset() == old(v)@.to_multiset());
    }
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
    /* code modified by LLM (iteration 5): selection-sort with strengthened invariants and proofs */
    let mut v = s.clone();
    let n: usize = v.len();

    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            forall|a: int, b: int| 0 <= a < b < (i as int) ==> popcount(v@[a] as nat) <= popcount(v@[b] as nat),
            forall|a: int, b: int| 0 <= a < (i as int) && (i as int) <= b < (n as int) ==> popcount(v@[a] as nat) <= popcount(v@[b] as nat),
            v@.to_multiset() == s@.to_multiset(),
        decreases (n as int) - (i as int)
    {
        let mut min_idx: usize = i;
        let mut j: usize = i + 1;
        while j < n
            invariant
                0 <= (i as int) <= (min_idx as int) < (n as int),
                (i as int) + 1 <= (j as int) <= (n as int),
                forall|a: int, b: int| 0 <= a < b < (i as int) ==> popcount(v@[a] as nat) <= popcount(v@[b] as nat),
                forall|k: int| (i as int) <= k < (j as int) ==> popcount(v@[(min_idx as int)] as nat) <= popcount(v@[k] as nat),
                v@.to_multiset() == s@.to_multiset(),
            decreases (n as int) - (j as int)
        {
            if v[j].count_ones() < v[min_idx].count_ones() {
                min_idx = j;
                proof {
                    // maintain minimality invariant by connecting runtime counts to spec popcount
                    lemma_popcount_u8(v[min_idx]);
                    lemma_popcount_u8(v[j]);
                    assert((v[j].count_ones() as nat) == popcount(v@[(j as int)] as nat));
                    assert((v[min_idx].count_ones() as nat) == popcount(v@[(min_idx as int)] as nat));
                }
            }
            j += 1;
        }

        // after inner loop, min_idx is minimal in [i..n)
        proof {
            let mut k: usize = i;
            while k < n
                invariant
                    i <= k && k <= n,
                decreases (n as int) - (k as int)
            {
                lemma_popcount_u8(v[min_idx]);
                lemma_popcount_u8(v[k]);
                k += 1;
            }
            assert(forall|k: int| (i as int) <= k < (n as int) ==> popcount(v@[(min_idx as int)] as nat) <= popcount(v@[k] as nat));
        }

        swap_vec_u8(&mut v, i, min_idx);
        // after swap, prefix [0..=i] is the set of smallest i+1 elements in sorted order
        proof {
            // prefix elements that were before remain sorted
            assert(forall|a: int, b: int| 0 <= a < b < (i as int) ==> popcount(v@[a] as nat) <= popcount(v@[b] as nat));
            // new element at i is the minimal of the suffix, and by outer invariant prefix elements are <= suffix
            assert(forall|a: int| 0 <= a < (i as int) ==> popcount(v@[a] as nat) <= popcount(v@[(i as int)] as nat));
            assert(v@.to_multiset() == s@.to_multiset());
        }

        i += 1;
    }

    v
}
// </vc-code>


}

fn main() {}