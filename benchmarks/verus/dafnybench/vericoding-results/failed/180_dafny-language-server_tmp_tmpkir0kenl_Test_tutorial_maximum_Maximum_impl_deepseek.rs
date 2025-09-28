use vstd::prelude::*;

verus! {

// This file shows how to specify and implement a function to compute the
// largest element of a list. The function is fully specified by two
// preconditions, as proved by the MaximumIsUnique lemma below.

// <vc-helpers>
proof fn MaximumIsUnique(values: Seq<int>, max1: int, max2: int)
    requires
        values.len() > 0,
        values.contains(max1),
        values.contains(max2),
        forall|i: int| 0 <= i < values.len() ==> values[i] <= max1,
        forall|i: int| 0 <= i < values.len() ==> values[i] <= max2,
    ensures
        max1 == max2,
{
    assert(values.contains(max1) && values.contains(max2));
    assert(max2 <= max1) by {
        let j = choose|j: int| 0 <= j < values.len() && values[j] == max2;
        assert(values[j] <= max1);
    };
    assert(max1 <= max2) by {
        let j = choose|j: int| 0 <= j < values.len() && values[j] == max1;
        assert(values[j] <= max2);
    };
}

proof fn lemma_seq_index_contains(values: Seq<int>, i: int)
    requires
        0 <= i < values.len(),
    ensures
        values.contains(values[i]),
{
}

proof fn lemma_seq_len_nat(values: Seq<int>) 
    ensures
        values.len() is nat,
{
}

proof fn lemma_cast_index(values: Seq<int>, index: usize)
    requires
        index < values.len() as usize,
    ensures
        0 <= index as int < values.len(),
{
}
// </vc-helpers>
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
    proof { lemma_seq_len_nat(values); }
    let mut current_max = values@[0];
    let mut index: usize = 1;
    
    while index < values.len() as usize
        invariant
            index <= values.len() as usize,
            0 < index,
            values.contains(current_max),
            forall|i: int| 0 <= i < index as int ==> values@[i] <= current_max,
    {
        proof { lemma_cast_index(values, index); }
        let elem = values@[index as int];
        if elem > current_max {
            current_max = elem;
        }
        proof {
            assert(values.contains(current_max)) by {
                if elem > current_max {
                    lemma_seq_index_contains(values, index as int);
                }
            };
        }
        index = index + 1;
    }
    
    // Final proof that current_max satisfies the postcondition
    proof {
        // Prove that all elements are <= current_max
        assert forall|j: int| 0 <= j < values.len() implies values@[j] <= current_max by {
            if j < index as int {
                // Covered by the loop invariant
            } else {
                assert(index as int == values.len() as int);
            }
        };
    }
    
    current_max
}
// </vc-code>

fn main() {}

}