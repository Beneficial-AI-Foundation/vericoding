// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): prove that prefix equality implies contains */
fn prefix_eq_contains(l: Seq<nat>, m: int, candidate: int)
    requires
        0 <= m <= l.len(),
        0 <= candidate < m,
        forall|i: int| 0 <= i < m ==> l[i] == (i as nat),
    ensures
        l.contains(candidate as nat),
{
    proof {
        // From the prefix equality we have l[candidate] == candidate
        assert(l[candidate] == (candidate as nat));
        // Thus the sequence contains candidate
        assert(l.contains(candidate as nat));
    }
}

/* helper modified by LLM (iteration 5): prove missing element after mismatch */
fn missing_after_mismatch(l: Seq<nat>, idx: int)
    requires
        0 < idx < l.len(),
        forall|i: int| 0 <= i < idx ==> l[i] == (i as nat),
        forall|i: int, j: int| 0 <= i < j < l.len() ==> l[i] < l[j],
        l[idx] != (idx as nat),
    ensures
        !l.contains(idx as nat),
{
    proof {
        // For j < idx: l[j] == j, hence l[j] < idx
        assert(forall|j: int| 0 <= j < idx ==> l[j] < (idx as nat));

        // From strict increasing property, l[idx] > l[idx-1]
        assert(l[idx] > l[idx - 1]);
        assert(l[idx - 1] == ((idx - 1) as nat));
        // So l[idx] >= idx
        assert(l[idx] >= (idx as nat));

        // Since l[idx] != idx, in fact l[idx] >= idx + 1
        assert(l[idx] >= ((idx as nat) + 1));

        // For j > idx: l[j] > l[idx] >= idx+1 > idx
        assert(forall|j: int| idx < j < l.len() ==> l[j] > (idx as nat));

        // Combine: no element equals idx
        assert(forall|j: int| 0 <= j < l.len() ==> l[j] != (idx as nat));

        // Therefore sequence does not contain idx
        assert(!l.contains(idx as nat));
    }
}

/* helper modified by LLM (iteration 5): prove zero is missing when first element is nonzero */
fn zero_missing(l: Seq<nat>)
    requires
        0 < l.len(),
        l[0] != 0,
        forall|i: int, j: int| 0 <= i < j < l.len() ==> l[i] < l[j],
    ensures
        !l.contains(0 as nat),
{
    proof {
        // l[0] != 0 implies l[0] >= 1
        assert(l[0] >= 1);
        // By monotonicity, all elements are >= l[0] >= 1
        assert(forall|j: int| 0 <= j < l.len() ==> l[j] >= l[0]);
        assert(forall|j: int| 0 <= j < l.len() ==> l[j] >= 1);
        // hence no element equals 0
        assert(forall|j: int| 0 <= j < l.len() ==> l[j] != 0);
        assert(!l.contains(0 as nat));
    }
}

// </vc-helpers>

// <vc-spec>
fn smallest_missing(l: Seq<nat>) -> (result: nat)
    requires forall|i: int, j: int| 0 <= i < j < l.len() ==> l[i] < l[j],
    ensures
        !l.contains(result),
        forall|candidate: nat| candidate < result ==> l.contains(candidate)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): iterate to find first missing element */
    let mut i: int = 0;
    while i < l.len()
        invariant
            0 <= i,
            i <= l.len(),
            forall|j: int| 0 <= j < i ==> l[j] == (j as nat),
        decreases l.len() - i
    {
        if l[i] != (i as nat) {
            if i == 0 {
                zero_missing(l);
                return 0;
            } else {
                missing_after_mismatch(l, i);
                return i as nat;
            }
        }
        i = i + 1;
    }

    // After the loop, every index j < l.len() satisfies l[j] == j
    proof {
        assert(forall|candidate: int| 0 <= candidate < l.len() ==> l[candidate] == (candidate as nat));
        // thus no element equals l.len()
        assert(forall|j: int| 0 <= j < l.len() ==> l[j] != (l.len() as nat));
        assert(!l.contains(l.len() as nat));
    }
    return l.len() as nat;
}

// </vc-code>

}
fn main() {}