use vstd::prelude::*;

verus! {

// Checks if array 'a' is sorted.
spec fn is_sorted(a: &[i32]) -> bool {
    forall|i: int, j: int| 0 <= i < j < a.len() ==> a[i] <= a[j]
}

// Finds a value 'x' in a sorted array 'a', and returns its index,
// or -1 if not found.

// Simple test cases to check the post-condition.

/*
a) Identify adequate pre and post-conditions for this method, 
and encode them as "requires" and "ensures" clauses in Verus. 
You can use the predicate below if needed.

b) Identify an adequate loop variant and loop invariant, and encode them 
as "decreases" and "invariant" clauses in Verus.
*/

// <vc-helpers>
spec fn contains(seq: Seq<i32>, x: i32) -> bool {
    exists|i: int| 0 <= i < seq.len() && seq[i] == x
}

proof fn lemma_contains_index(seq: Seq<i32>, x: i32, i: int)
    requires
        0 <= i < seq.len(),
        seq[i] == x,
    ensures
        contains(seq, x)
{
}

proof fn lemma_not_contains(seq: Seq<i32>, x: i32)
    requires
        forall|k: int| 0 <= k < seq.len() ==> seq[k] != x,
    ensures
        !contains(seq, x)
{
}

proof fn lemma_sorted_property(a: Seq<i32>, i: int, j: int)
    requires
        is_sorted_slice(a),
        0 <= i <= j < a.len(),
    ensures
        a[i] <= a[j]
{
}

proof fn lemma_sorted_property_lower_bound(a: Seq<i32>, i: int, j: int)
    requires
        is_sorted_slice(a),
        0 <= i < a.len(),
        0 <= j < a.len(),
        i <= j,
    ensures
        a[i] <= a[j]
{
}

spec fn is_sorted_slice(seq: Seq<i32>) -> bool {
    forall|i: int, j: int| 0 <= i < j < seq.len() ==> seq[i] <= seq[j]
}

proof fn lemma_array_sorted_implies_sequence_sorted(a: &[i32])
    requires
        is_sorted(a),
    ensures
        is_sorted_slice(a@)
{
}

proof fn lemma_sequence_equality(a: &[i32], i: int)
    requires
        0 <= i < a.len() as int,
    ensures
        a@[i] == a[i as usize]
{
}

proof fn lemma_index_cast(result: i32, len: usize)
    requires
        result >= 0,
        (result as usize) < len,
    ensures
        (result as int) >= 0 && (result as usize) < len
{
}
// </vc-helpers>

// <vc-spec>
fn binary_search(a: &[i32], x: i32) -> (index: i32)
    requires is_sorted(a)
    ensures -1 <= index < a.len() && 
            (index != -1 ==> a[index as int] == x) &&
            (index == -1 ==> !a@.contains(x))
// </vc-spec>
// <vc-code>
{
    proof {
        lemma_array_sorted_implies_sequence_sorted(a);
    }
    let mut low: usize = 0;
    let mut high: usize = a.len();
    let mut result: i32 = -1;
    
    while low < high
        invariant
            low <= high <= a.len(),
            result >= -1 && result < a.len() as i32,
            (result != -1 ==> (result as int) >= 0 && (result as usize) < a.len() && a[result as usize] == x),
            (result == -1 ==> forall|k: int| 0 <= k < low as int || high as int <= k < a.len() as int ==> a@[k] != x),
            is_sorted_slice(a@)
        decreases high - low
    {
        let mid = low + (high - low) / 2;
        proof {
            lemma_sequence_equality(a, mid as int);
        }
        if a[mid] == x {
            result = mid as i32;
            break;
        } else if a[mid] < x {
            proof {
                lemma_sorted_property(a@, low as int, mid as int);
            }
            low = mid + 1;
        } else {
            proof {
                lemma_sorted_property(a@, mid as int, (high - 1) as int);
            }
            high = mid;
        }
    }
    
    if result != -1 {
        proof {
            lemma_index_cast(result, a.len());
        }
    }
    result
}
// </vc-code>

fn main() {
}

}