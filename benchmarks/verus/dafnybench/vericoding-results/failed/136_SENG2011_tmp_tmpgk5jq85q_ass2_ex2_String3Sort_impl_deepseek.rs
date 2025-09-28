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
spec fn swap(a: Seq<char>, i: int, j: int) -> Seq<char>
    recommends 0 <= i < a.len(), 0 <= j < a.len()
{
    a.update(i, a[j]).update(j, a[i])
}

proof fn swap_preserves_multiset(a: Seq<char>, i: int, j: int)
    requires 0 <= i < a.len(), 0 <= j < a.len()
    ensures swap(a, i, j).to_multiset() == a.to_multiset()
{
    assert forall|k: int| #![trigger a.index(k)] 0 <= k < a.len() implies swap(a, i, j).index(k) == a.index(k) || k == i || k == j by {
        if k == i {
            assert(swap(a, i, j)[k] == a[j]);
        } else if k == j {
            assert(swap(a, i, j)[k] == a[i]);
        } else {
            assert(swap(a, i, j)[k] == a[k]);
        }
    };
    assert(swap(a, i, j).to_multiset() =~= a.to_multiset());
}

proof fn swap_sorted(a: Seq<char>, i: int, j: int, low: int, high: int)
    requires 
        0 <= low <= high <= a.len(),
        sorted(a, low, high),
        0 <= i < a.len(), 0 <= j < a.len(),
        i >= low, i < high, j >= low, j < high
    ensures sorted(swap(a, i, j), low, high)
{
}

proof fn sorted_transitivity(a: Seq<char>, i: int, j: int, k: int)
    requires 
        0 <= i <= j <= k <= a.len(),
        sorted(a, i, j),
        sorted(a, j, k),
        a[j-1] <= a[j]
    ensures sorted(a, i, k)
{
}

proof fn sorted_extends(a: Seq<char>, i: int, j: int, k: int)
    requires 
        0 <= i <= j <= k <= a.len(),
        sorted(a, i, j),
        forall|m: int| j <= m < k ==> a[j-1] <= a[m]
    ensures sorted(a, i, k)
{
}

proof fn sorted_two_elements(a: Seq<char>, i: int)
    requires 0 <= i < a.len() - 1, a[i] <= a[i+1]
    ensures sorted(a, i, i+2)
{
}

proof fn sorted_three_elements(a: Seq<char>, i: int)
    requires 0 <= i < a.len() - 2, a[i] <= a[i+1], a[i+1] <= a[i+2]
    ensures sorted(a, i, i+3)
{
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
    let mut b = a;
    
    proof {
        // First compare and potentially swap elements 0 and 1
        if a[0] > a[1] {
            let old_b = b;
            b = swap(old_b, 0, 1);
            swap_preserves_multiset(old_b, 0, 1);
            assert(b.to_multiset() == old_b.to_multiset());
            assert(b[0] <= b[1]);
            sorted_two_elements(b, 0);
        } else {
            assert(b[0] <= b[1]);
            sorted_two_elements(b, 0);
        }
    }
    
    proof {
        // Compare and potentially swap elements 1 and 2
        if b[1] > b[2] {
            let old_b = b;
            b = swap(old_b, 1, 2);
            swap_preserves_multiset(old_b, 1, 2);
            assert(b.to_multiset() == old_b.to_multiset());
            assert(b[1] <= b[2]);
            
            // Now check if we need to swap elements 0 and 1 again
            if b[0] > b[1] {
                let old_b2 = b;
                b = swap(old_b2, 0, 1);
                swap_preserves_multiset(old_b2, 0, 1);
                assert(b.to_multiset() == old_b2.to_multiset());
                assert(b[0] <= b[1]);
                assert(b[1] <= b[2]);
                sorted_three_elements(b, 0);
            } else {
                assert(b[0] <= b[1]);
                assert(b[1] <= b[2]);
                sorted_three_elements(b, 0);
            }
        } else {
            assert(b[1] <= b[2]);
            assert(b[0] <= b[1]);
            assert(b[0] <= b[2]);
            sorted_three_elements(b, 0);
        }
    }
    
    assert(sorted(b, 0, 3));
    assert(b.len() == 3);
    assert(b.to_multiset() == a.to_multiset());
    
    b
}
// </vc-code>

fn main() {
}

}