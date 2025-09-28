use vstd::prelude::*;

verus! {

///////////////////
// Binary search
///////////////////


spec fn is_sorted(a: &[int]) -> bool {
    forall|i: int, j: int| 0 <= i <= j < a.len() ==> a[i] <= a[j]
}


// a[lo] <= a[lo+1] <= ... <= a[hi-2] <= a[hi-1]

/* Note: the following definition of is_sorted:


although equivalent to the one above is not enough for Verus to be able 
to prove the invariants for the loop in bin_search.

The given one works because it *explicitly* states that every element 
of the input array is smaller than or equal to all later elements. 
This fact is implied by the alternative definition of is_sorted given 
here (which only talks about array elements and their successors). 
However, it needs to be derived as an auxiliary lemma first, something 
that Verus is not currently able to do automatically. 
*/

// <vc-helpers>
proof fn sorted_property(a: &[int], i: int, j: int)
    requires
        is_sorted(a),
        0 <= i <= j < a.len(),
    ensures
        a[i] <= a[j]
{
}

proof fn not_found_in_range(a: &[int], k: int, lo: int, hi: int)
    requires
        is_sorted(a),
        0 <= lo <= hi <= a.len(),
        hi > 0 ==> a[hi - 1] < k,
        lo < a.len() ==> a[lo] > k,
    ensures
        forall|i: int| lo <= i < hi ==> a[i] != k
{
    if lo < hi {
        assert(forall|i: int| lo <= i < hi ==> {
            &&& (lo < a.len() ==> a[lo] <= #[trigger] a[i])
            &&& (hi > 0 ==> #[trigger] a[i] <= a[hi - 1])
            &&& (lo < a.len() && hi > 0 ==> a[lo] > k && a[hi - 1] < k)
            &&& a[i] != k
        });
    }
}
// </vc-helpers>

// <vc-spec>
fn bin_search(a: &[int], k: int) -> (b: bool)
    requires is_sorted(a)
    ensures b == exists|i: int| 0 <= i < a.len() && a[i] == k
// </vc-spec>
// <vc-code>
{
    if a.len() == 0 {
        return false;
    }
    
    let mut lo: usize = 0;
    let mut hi: usize = a.len();
    
    while lo < hi
        invariant
            0 <= lo <= hi <= a.len(),
            is_sorted(a),
            forall|i: int| 0 <= i < lo ==> a[i] < k,
            forall|i: int| hi <= i < a.len() ==> a[i] > k,
            (exists|i: int| 0 <= i < a.len() && a[i] == k) <==> (exists|i: int| lo <= i < hi && a[i] == k)
        decreases hi - lo
    {
        let mid = lo + (hi - lo) / 2;
        
        if a[mid] == k {
            return true;
        } else if a[mid] < k {
            lo = mid + 1;
        } else {
            hi = mid;
        }
    }
    
    proof {
        not_found_in_range(a, k, lo as int, hi as int);
    }
    
    false
}
// </vc-code>

fn main() {
}

}