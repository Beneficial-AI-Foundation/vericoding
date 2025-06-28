use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn Sorted(q: Seq<int>) -> bool {
    forall|i: int, j: int| 0 <= i <= j < q.len() ==> q[i] <= q[j]
}

// Helper function to check if a sequence is sorted (executable version)
fn is_sorted(q: &Vec<i32>) -> (result: bool)
    ensures result == Sorted(q@)
{
    if q.len() <= 1 {
        return true;
    }
    
    let mut i = 0;
    while i < q.len() - 1
        invariant 
            0 <= i <= q.len() - 1,
            forall|k: int, l: int| 0 <= k <= l < i + 1 ==> q@[k] <= q@[l]
    {
        if q[i] > q[i + 1] {
            return false;
        }
        i += 1;
    }
    true
}

// Proof function demonstrating properties of sorted sequences
proof fn sorted_empty_and_single()
    ensures Sorted(Seq::<int>::empty())
    ensures forall|x: int| Sorted(seq![x])
{
}

// Proof function showing that subsequences of sorted sequences are sorted
proof fn sorted_subsequence(q: Seq<int>, start: int, end: int)
    requires Sorted(q)
    requires 0 <= start <= end <= q.len()
    ensures Sorted(q.subrange(start, end))
{
}

}