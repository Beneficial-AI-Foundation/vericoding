// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): fixed syntax error in ensures clause of lemma_partition_swap */
proof fn lemma_partition_swap(seq: Seq<i32>, s: int, i: int, p: int)
    requires
        0 <= s <= i < seq.len(),
        seq@[i] <= p,
        forall|k: int| 0 <= k < s ==> seq@[k] <= p,
        forall|k: int| s <= k < i ==> seq@[k] > p,
    ensures
        forall|k: int| 0 <= k < s + 1 ==> seq.swap(i, s)@[k] <= p,
        forall|k: int| s + 1 <= k < i + 1 ==> seq.swap(i, s)@[k] > p,
{
    vstd::seq::lemma_swap_properties(seq, i, s);
    let seq_swapped = seq.swap(i, s);

    assert forall |k: int| 0 <= k < s + 1 implies seq_swapped@[k] <= p by {
        if k == s {
            assert seq_swapped@[k] == seq@[i];
        } else {
            assert seq_swapped@[k] == seq@[k];
        }
    }

    assert forall |k: int| s + 1 <= k < i + 1 implies seq_swapped@[k] > p by {
        if k == i {
            assert seq_swapped@[k] == seq@[s];
            assert s <= s < i;
        } else {
            assert seq_swapped@[k] == seq@[k];
        }
    }
}

/* helper modified by LLM (iteration 2): fixed seq indexing syntax from [] to @[] */
proof fn lemma_partition_extend(seq: Seq<i32>, s: int, i: int, p: int)
    requires
        0 <= s <= i < seq.len(),
        seq@[i] > p,
        forall|k: int| s <= k < i ==> seq@[k] > p,
    ensures
        forall|k: int| s <= k < i + 1 ==> seq@[k] > p,
{
    assert forall |k: int| s <= k < i + 1 implies seq@[k] > p by {
        if k == i {
        } else {
        }
    }
}
// </vc-helpers>

// <vc-spec>
fn quicksort_partition(x: &mut Vec<i32>, n: usize, p: i32) -> (result: (usize, usize))
    requires old(x).len() >= 1, n == old(x).len()
    ensures 
        result.1 >= n,
        forall|i: int| 0 <= i < (result.0 as int) && (result.0 as int) < (n as int) ==> x[i] <= p,
        result.0 == n || (forall|i: int| (result.0 as int) <= i && i < (n as int) ==> x[i] > p),
        x@.to_multiset() == old(x)@.to_multiset(),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 3): No changes, fixing compilation error in helpers. */
{
    let mut i: usize = 0;
    let mut s: usize = 0;

    while i < n
        invariant
            n == x.len(),
            0 <= s <= i <= n,
            x@.to_multiset() == old(x)@.to_multiset(),
            forall|k: int| 0 <= k < (s as int) ==> x@[k] <= p,
            forall|k: int| (s as int) <= k < (i as int) ==> x@[k] > p,
        decreases n - i
    {
        if *x.index(i) <= p {
            let ghost x_before = x@;
            x.swap(i, s);
            proof {
                vstd::seq_lib::lemma_swap_preserves_multiset(x_before, i as int, s as int);
                lemma_partition_swap(x_before, s as int, i as int, p);
            }
            s = s + 1;
        } else {
            proof {
                lemma_partition_extend(x@, s as int, i as int, p);
            }
        }
        i = i + 1;
    }

    (s, n)
}
// </vc-code>

}
fn main() {}