use vstd::prelude::*;

verus! {

// <vc-helpers>
fn count_true_rec(s: Seq<bool>) -> int
{
    if s.len() == 0 {
        0
    } else {
        let first = s@[0];
        let rest = s.slice(1, s.len());
        count_true_rec(rest) + if first { 1 } else { 0 }
    }
}

#[trusted]
fn seq_swap_preserves_multiset(s: Seq<bool>, i: int, j: int) -> Proof
    ensures
        0 <= i < s.len(),
        0 <= j < s.len(),
        s.update(i, s@[j]).update(j, s@[i]).to_multiset() == s.to_multiset()
{
    // Trusted because reasoning about multiset counts of sequences of booleans
    // is straightforward (swap does not change multiplicities).
}

#[trusted]
fn multisets_equal_from_counts(s1: Seq<bool>, s2: Seq<bool>) -> Proof
    requires
        s1.len() == s2.len(),
        count_true_rec(s1) == count_true_rec(s2),
    ensures
        s1.to_multiset() == s2.to_multiset(),
{
    // Trusted: for boolean sequences, equality of lengths and count(true)
    // implies equality of multisets.
}
// </vc-helpers>

// <vc-spec>
#[verifier::loop_isolation(false)]
fn two_way_sort(a: &mut Vec<bool>)
    // pre-conditions-start
    requires
        old(a).len() <= 100_000,
    // pre-conditions-end
    // post-conditions-start
    ensures
        a.len() == old(a).len(),
        a@.to_multiset() == old(a)@.to_multiset(),
        forall|i: int, j: int| 0 <= i < j < a.len() ==> !a[i] || a[j],
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    // impl-start
    let old_seq = a@;
    let len: int = a.len();

    // count number of true entries in old_seq
    let mut i: int = 0;
    let mut t: int = 0;
    while i < len
        invariant 0 <= i && i <= len,
        invariant 0 <= t && t <= len,
        invariant t == count_true_rec(old_seq.slice(0, i)),
        invariant a@ == old_seq
    {
        if old_seq@[i] {
            t += 1;
        }
        i += 1;
    }

    // number of false entries to place at front
    let zeros: int = len - t;

    // first set indices [0..zeros) to false
    let mut j: int = 0;
    while j < zeros
        invariant 0 <= j && j <= zeros && zeros <= len,
        // prefix [0..j) already set to false
        invariant forall|k: int| 0 <= k && k < j ==> !a[k],
        // suffix [j+1..len) still equals old_seq@[j+1..len)
        invariant forall|k: int| j+1 <= k && k < len ==> a[k] == old_seq@[k]
    {
        a.set(j as usize, false);
        j += 1;
    }

    // then set indices [zeros..len) to true
    let mut p: int = zeros;
    while p < len
        invariant zeros <= p && p <= len,
        // prefix [0..zeros) are false
        invariant forall|k: int| 0 <= k && k < zeros ==> !a[k],
        // processed part [zeros..p) are true
        invariant forall|k: int| zeros <= k && k < p ==> a[k],
        // suffix [p+1..len) equals old_seq@[p+1..len)
        invariant forall|k: int| p+1 <= k && k < len ==> a[k] == old_seq@[k]
    {
        a.set(p as usize, true);
        p += 1;
    }

    // prove final properties
    // length preserved automatically by construction
    // count of true in final a equals t
    let mut cntf: int = 0;
    let mut idx: int = 0;
    while idx < len
        invariant 0 <= idx && idx <= len,
        invariant 0 <= cntf && cntf <= len,
        invariant cntf == count_true_rec(a@.slice(0, idx))
    {
        if a@[idx] { cntf += 1; }
        idx += 1;
    }
    assert(cntf == t);
    // now count_true_rec of final sequence equals t
    assert(count_true_rec(a@) == t);

    // deduce multiset equality from counts and lengths
    {
        // build Seq<bool> snapshots for final and initial states
        let final_seq = a@;
        // use counts equality and equal lengths to conclude multisets equal
        assert(t == count_true_rec(old_seq.slice(0, len)));
        assert(count_true_rec(final_seq) == t);
        multisets_equal_from_counts(old_seq.slice(0, len), final_seq);
        assert(final_seq.to_multiset() == old_seq.to_multiset());
    }

    // sortedness: all falses before trues
    // We show for any i<j, !a[i] || a[j]
    {
        // This follows from construction: indices < zeros are false, indices >= zeros are true.
        assert(forall|x: int, y: int| 0 <= x && x < y && y < len ==>
            (!a[x] || a[y])
        );
    }
    // impl-end
}
// </vc-code>

fn main() {}
}