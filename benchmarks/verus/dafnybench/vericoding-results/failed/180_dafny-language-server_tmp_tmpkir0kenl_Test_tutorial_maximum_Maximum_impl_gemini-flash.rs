use vstd::prelude::*;

verus! {

// This file shows how to specify and implement a function to compute the
// largest element of a list. The function is fully specified by two
// preconditions, as proved by the MaximumIsUnique lemma below.

// <vc-helpers>
lemma fn MaximumIsUnique(values: Seq<int>, m1: int, m2: int)
    requires
        values.len() > 0,
        values.contains(m1),
        forall|i: int| 0 <= i < values.len() ==> values[i] <= m1,
        values.contains(m2),
        forall|i: int| 0 <= i < values.len() ==> values[i] <= m2,
    ensures
        m1 == m2,
{
    // If m1 is a maximum, since m2 is in the sequence, m2 <= m1.
    // If m2 is a maximum, since m1 is in the sequence, m1 <= m2.
    // Together, m1 == m2.
    assert(m2 <= m1) by {
        // m2 is in the sequence, say at index k: values[k] == m2.
        // Since m1 is a maximum, forall i, values[i] <= m1.
        // Thus, values[k] <= m1, which means m2 <= m1.
        let (k, _) = values.find(|_k_idx, _k_val| _k_val == m2).unwrap();
        assert(values[k] == m2);
        assert(values[k] <= m1); // from the universal quantifier for m1
    }
    assert(m1 <= m2) by {
        // m1 is in the sequence, say at index k: values[k] == m1.
        // Since m2 is a maximum, forall i, values[i] <= m2.
        // Thus, values[k] <= m2, which means m1 <= m2.
        let (k, _) = values.find(|_k_idx, _k_val| _k_val == m1).unwrap();
        assert(values[k] == m1);
        assert(values[k] <= m2); // from the universal quantifier for m2
    }
}

#[verifier(external_body)] // This is an external specification for the maximum function in Rust.
fn rust_maximum(values: &[i32]) -> i32 {
    let mut max_val = values[0];
    for &x in values.iter() {
        if x > max_val {
            max_val = x;
        }
    }
    max_val
}
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
    let mut max_val: int = values.index(0);
    let mut i: int = 1;

    // Proof snippet to show that values.index(0) is a value from the sequence
    proof {
        assert(values.contains(max_val)) by {
            // Since max_val = values.index(0), and 0 is a valid index, max_val is in the sequence.
            assert(0 <= 0 && 0 < values.len()); // This is true by precondition values.len() > 0
            assert(values.index(0) == max_val);
            assert(values.contains(values.index(0)));
        }
    }

    while i < values.len()
        invariant
            0 < values.len(),
            values.contains(max_val),
            0 <= i && i <= values.len(),
            forall|k: int| 0 <= k < i ==> values.index(k) <= max_val,
    {
        if values.index(i) > max_val {
            max_val = values.index(i);
            proof {
                assert(values.contains(max_val)) by {
                    assert(values.index(i) == max_val);
                    assert(values.contains(values.index(i)));
                }
            }
        }
        i = i + 1;
    }
    max_val
}
// </vc-code>

fn main() {}

}