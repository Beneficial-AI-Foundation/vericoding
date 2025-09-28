use vstd::prelude::*;

verus! {

// verifies
// check that string between indexes low and high-1 are sorted
spec fn sorted(a: Seq<char>, low: int, high: int) -> bool
    recommends 0 <= low <= high <= a.len()
{ 
    forall|j: int, k: int| low <= j < k < high ==> a[j] <= a[k]
}

// <vc-helpers>
// Helper lemma to prove that manually constructed sequence preserves multiset
proof fn multiset_preserved_3(a: Seq<char>, b: Seq<char>)
    requires
        a.len() == 3,
        b.len() == 3,
    ensures
        seq![b[0], b[1], b[2]].to_multiset() == seq![a[0], a[1], a[2]].to_multiset()
            <==> b.to_multiset() == a.to_multiset()
{
    assert(seq![b[0], b[1], b[2]] =~= b);
    assert(seq![a[0], a[1], a[2]] =~= a);
}
// </vc-helpers>

// <vc-spec>
fn string3_sort(a: Seq<char>) -> (b: Seq<char>)
    requires 
        a.len() == 3,
    ensures 
        sorted(b, 0, b.len() as int),
        a.len() == b.len(),
        seq![b[0], b[1], b[2]].to_multiset() == seq![a[0], a[1], a[2]].to_multiset(),
// </vc-spec>
// <vc-code>
{
    // Compare all three elements and determine their sorted order
    let (min, mid, max) = if a[0] <= a[1] {
        if a[1] <= a[2] {
            // a[0] <= a[1] <= a[2]
            (a[0], a[1], a[2])
        } else if a[0] <= a[2] {
            // a[0] <= a[2] < a[1]
            (a[0], a[2], a[1])
        } else {
            // a[2] < a[0] <= a[1]
            (a[2], a[0], a[1])
        }
    } else {
        // a[1] < a[0]
        if a[0] <= a[2] {
            // a[1] < a[0] <= a[2]
            (a[1], a[0], a[2])
        } else if a[1] <= a[2] {
            // a[1] <= a[2] < a[0]
            (a[1], a[2], a[0])
        } else {
            // a[2] < a[1] < a[0]
            (a[2], a[1], a[0])
        }
    };
    
    let result = seq![min, mid, max];
    
    // Prove that result is sorted
    assert forall|j: int, k: int| 0 <= j < k < 3 implies result[j] <= result[k] by {
        assert(min <= mid);
        assert(mid <= max);
        assert(min <= max);
        if j == 0 && k == 1 {
            assert(result[j] == min);
            assert(result[k] == mid);
        } else if j == 0 && k == 2 {
            assert(result[j] == min);
            assert(result[k] == max);
        } else if j == 1 && k == 2 {
            assert(result[j] == mid);
            assert(result[k] == max);
        }
    }
    assert(sorted(result, 0, result.len() as int));
    
    // Prove multiset preservation
    proof {
        multiset_preserved_3(a, result);
    }
    
    result
}
// </vc-code>

fn main() {
}

}