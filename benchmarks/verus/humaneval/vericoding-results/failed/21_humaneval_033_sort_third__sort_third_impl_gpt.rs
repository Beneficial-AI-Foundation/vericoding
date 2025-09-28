// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): prove that swapping two indices of a sequence preserves its multiset */
proof fn lemma_mset_preserved_by_swap_pair(s: Seq<i8>, i: int, j: int)
    requires
        0 <= i < s.len(),
        0 <= j < s.len(),
        i != j,
    ensures
        s.update(i, s[j]).update(j, s[i]).to_multiset() == s.to_multiset(),
{
    let t = s.update(i, s[j]).update(j, s[i]);

    // Basic properties of updates at indices different from i and j
    assert forall|k: int| 0 <= k < s.len() && k != i ==> s.update(i, s[j])[k] == s[k] by { };
    assert forall|k: int| 0 <= k < s.len() && k != j ==> t[k] == s.update(i, s[j])[k] by { };

    // Values at the swapped positions
    assert(t[i] == s[j]);
    assert(t[j] == s[i]);

    // Length preserved
    assert(t.len() == s.len());

    // Show equality of multisets by pointwise equality of counts
    assert forall|x: i8| t.to_multiset().count(x) == s.to_multiset().count(x) by {
        // Only positions i and j can affect multiplicities; others are unchanged
        // This follows from the definition of to_multiset for sequences and the behavior of update
    };
}

// </vc-helpers>

// <vc-spec>
fn sort_third(a: &Vec<i8>) -> (sorted_even: Vec<i8>)
    requires a@.len() > 0
    ensures 
        sorted_even@.len() == a@.len(),
        forall|i: int, j: int| 0 <= i < j < sorted_even@.len() && i % 3 == 0 && j % 3 == 0 ==>
            sorted_even@[i] <= sorted_even@[j],
        forall|i: int| 0 <= i < a@.len() && i % 3 != 0 ==> sorted_even@[i] == a@[i],
        a@.to_multiset() == sorted_even@.to_multiset()
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): selection-sort only indices divisible by 3; strengthened invariants and added bounds asserts */
    let mut v: Vec<i8> = a.clone();
    let n: usize = v.len();

    let mut i: usize = 0;
    while i < n
        invariant
            v@.len() == n as int,
            a@.len() == n as int,
            a@.to_multiset() == v@.to_multiset(),
            0 <= (i as int) <= (n as int),
            (i as int) % 3 == 0,
            // Non-multiples-of-3 never change
            forall|t: int| 0 <= t < n as int && t % 3 != 0 ==> v@[t] == a@[t],
            // The prefix at multiples of 3 is sorted
            forall|p: int, q: int| 0 <= p < q < i as int && p % 3 == 0 && q % 3 == 0 ==> v@[p] <= v@[q],
            // Every element in the sorted prefix is <= any remaining element at multiples of 3
            forall|p: int, r: int|
                0 <= p < i as int && p % 3 == 0 && i as int <= r < n as int && r % 3 == 0 ==> v@[p] <= v@[r],
        decreases (n as int) - (i as int)
    {
        let mut j: usize = i;
        // Initialize k carefully to avoid usize overflow
        let mut k: usize;
        if n >= 3 {
            if i <= n - 3 { k = i + 3; } else { k = n; }
        } else {
            k = n;
        }
        while k < n
            invariant
                v@.len() == n as int,
                0 <= (i as int) <= (j as int) < (n as int),
                (k as int) <= (n as int),
                (i as int) % 3 == 0,
                (j as int) % 3 == 0,
                (k as int) % 3 == 0 || k == n, // k may be n at loop end
                // j holds the index of a minimum among scanned multiples of 3 so far
                forall|r: int|
                    (i as int) <= r && r < (k as int) && r < (n as int) && r % 3 == 0 ==> v@[j as int] <= v@[r],
                // Non-multiples-of-3 remain unchanged
                forall|t: int| 0 <= t < n as int && t % 3 != 0 ==> v@[t] == a@[t],
            decreases (n as int) - (k as int)
        {
            // Establish bounds for indexing
            proof {
                assert(v@.len() == n as int);
                assert((k as int) < (n as int));
                assert((j as int) < (n as int));
            }
            if v[k] < v[j] {
                j = k;
            }
            // Advance k by 3 without risking overflow
            if n >= 3 {
                if k <= n - 3 { k = k + 3; } else { k = n; }
            } else {
                k = n;
            }
        }
        if j != i {
            let ghost pre = v@;
            // Bounds for reading
            proof { assert(v@.len() == n as int); assert((i as int) < (n as int)); assert((j as int) < (n as int)); }
            let xi: i8 = v[i];
            let xj: i8 = v[j];
            v.set(i, xj);
            v.set(j, xi);
            proof {
                assert(xj == pre[j as int]);
                assert(xi == pre[i as int]);
                // After the two sets, v@ equals pre with a swap at i and j
                lemma_mset_preserved_by_swap_pair(pre, i as int, j as int);
            }
        }
        // Advance i by 3 without risking overflow
        if n >= 3 {
            if i <= n - 3 { i = i + 3; } else { i = n; }
        } else {
            i = n;
        }
    }

    v
}
// </vc-code>


}

fn main() {}