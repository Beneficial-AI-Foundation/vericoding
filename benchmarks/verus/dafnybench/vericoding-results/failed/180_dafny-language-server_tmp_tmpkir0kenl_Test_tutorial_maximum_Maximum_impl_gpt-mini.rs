use vstd::prelude::*;

verus! {

// This file shows how to specify and implement a function to compute the
// largest element of a list. The function is fully specified by two
// preconditions, as proved by the MaximumIsUnique lemma below.

// <vc-helpers>
// (no helpers needed)
// </vc-helpers>

// <vc-spec>
fn maximum(values: Seq<int>) -> (max: int)
    requires
        values.len() > 0,
    ensures
        values.contains(max),
        forall|i: int| 0 <= i < values.len() ==> values[i] <= max,
// </vc-spec>
// <vc-code>
{
    let mut i: int = 1;
    let mut m: int = values[0];

    // Establish loop invariants for the initial state (i = 1, m = values[0])
    proof {
        // 0 <= i && i <= values.len()
        assert(0 <= i && i <= values.len() as int);
        // forall j < 1, values[j] <= m
        assert(forall |j: int| 0 <= j < 1 ==> values[j] <= m);
        // exists j < 1 with values[j] == m (namely j = 0)
        assert(exists |j: int| 0 <= j < 1 && values[j] == m);
    };

    while i < values.len() as int
        invariant 0 <= i && i <= values.len() as int;
        invariant forall |j: int| 0 <= j < i ==> values[j] <= m;
        invariant exists |j: int| 0 <= j < i && values[j] == m;
        decreases values.len() as int - i;
    {
        if values[i] > m {
            // When we update m to values[i], prove invariants for i+1
            let old_m = m;
            let cur = values[i];
            // update
            m = cur;
            proof {
                // cur > old_m by the branch condition
                assert(cur > old_m);
                // For j < i, values[j] <= old_m (from invariant); thus values[j] <= cur = m
                assert(forall |j: int| 0 <= j < i ==> values[j] <= m);
                // values[i] == m
                assert(values[i] == m);
                // So forall j < i+1 values[j] <= m
                assert(forall |j: int| 0 <= j < i+1 ==> values[j] <= m);
                // Existence: j = i has values[i] == m
                assert(exists |j: int| 0 <= j < i+1 && values[j] == m);
            }
        } else {
            // m unchanged; prove invariants for i+1
            proof {
                // For j < i, values[j] <= m holds from invariant
                assert(forall |j: int| 0 <= j < i ==> values[j] <= m);
                // For j = i, values[i] <= m because not (values[i] > m)
                assert(values[i] <= m);
                // Thus forall j < i+1 values[j] <= m
                assert(forall |j: int| 0 <= j < i+1 ==> values[j] <= m);
                // Existence: previous existence for j < i still holds (and j < i+1)
                assert(exists |j: int| 0 <= j < i && values[j] == m);
                assert(exists |j: int| 0 <= j < i+1 && values[j] == m);
            }
        }

        i = i + 1;
    }

    // At loop exit i == values.len(), use invariants to conclude the postconditions
    proof {
        // From invariant: forall j < values.len() values[j] <= m
        assert(forall |j: int| 0 <= j < values.len() as int ==> values[j] <= m);
        // From invariant: exists j < values.len() with values[j] == m
        assert(exists |j: int| 0 <= j < values.len() as int && values[j] == m);
    };

    m
}
// </vc-code>

fn main() {}

}