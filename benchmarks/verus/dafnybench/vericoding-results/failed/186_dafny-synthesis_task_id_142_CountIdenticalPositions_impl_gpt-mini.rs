use vstd::prelude::*;

verus! {

// <vc-helpers>
fn lemma_set_extend(a: Seq<int>, b: Seq<int>, c: Seq<int>, i: nat)
    requires
        i < a.len()
    ensures
        Set::<int>::new(|k: int| 0 <= k && k < ((i + 1) as int) && a[k] == b[k] && b[k] == c[k]).len()
            == Set::<int>::new(|k: int| 0 <= k && k < (i as int) && a[k] == b[k] && b[k] == c[k]).len()
                + (if a[(i as int)] == b[(i as int)] && b[(i as int)] == c[(i as int)] { 1usize } else { 0usize })
{
    proof {
        let S_small = Set::<int>::new(|k: int| 0 <= k && k < (i as int) && a[k] == b[k] && b[k] == c[k]);
        let S_i = Set::<int>::new(|k: int| k == (i as int) && a[k] == b[k] && b[k] == c[k]);
        let S_large = Set::<int>::new(|k: int| 0 <= k && k < ((i + 1) as int) && a[k] == b[k] && b[k] == c[k]);

        assert(forall |k: int| S_large.contains(k) == (S_small.contains(k) || S_i.contains(k)));

        // S_small and S_i are disjoint
        assert(!exists(|k: int| S_small.contains(k) && S_i.contains(k)));

        // therefore S_large is the union of S_small and S_i
        assert(S_large == S_small.union(S_i));

        // union of disjoint sets has length equal to sum of lengths
        assert(S_large.len() == (S_small.union(S_i)).len());
        assert((S_small.union(S_i)).len() == S_small.len() + S_i.len());

        // S_i has length 1 exactly when the predicate holds at i, otherwise 0
        assert(S_i.len() == (if a[(i as int)] == b[(i as int)] && b[(i as int)] == c[(i as int)] { 1usize } else { 0usize }));

        assert(S_large.len() == S_small.len() + (if a[(i as int)] == b[(i as int)] && b[(i as int)] == c[(i as int)] { 1usize } else { 0usize }));
    }
}
// </vc-helpers>

// <vc-spec>
fn count_identical_positions(a: Seq<int>, b: Seq<int>, c: Seq<int>) -> (count: usize)
    requires
        a.len() == b.len() && b.len() == c.len(),
    ensures
        count >= 0,
        count == Set::<int>::new(|i: int| 0 <= i < a.len() && a[i] == b[i] && b[i] == c[i]).len(),
// </vc-spec>
// <vc-code>
{
    let n: nat = a.len();
    let mut i: nat = 0;
    let mut count: usize = 0usize;

    while i < n
        invariant i <= n;
        invariant count == Set::<int>::new(|k: int| 0 <= k && k < (i as int) && a[k] == b[k] && b[k] == c[k]).len();
        decreases (n - i);
    {
        let prev_count: usize = count;

        if a[(i as int)] == b[(i as int)] && b[(i as int)] == c[(i as int)] {
            count = count + 1;
        }

        // update ghost facts for the next index
        lemma_set_extend(a, b, c, i);

        assert(prev_count == Set::<int>::new(|k: int| 0 <= k && k < (i as int) && a[k] == b[k] && b[k] == c[k]).len());
        assert(count == Set::<int>::new(|k: int| 0 <= k && k < ((i + 1) as int) && a[k] == b[k] && b[k] == c[k]).len());

        i = i + 1;
    }

    count
}
// </vc-code>

fn main() {
}

}