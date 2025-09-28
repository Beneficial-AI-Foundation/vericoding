use vstd::prelude::*;

verus! {

// <vc-helpers>
// No additional helpers needed for this implementation
// </vc-helpers>

// <vc-spec>
fn reverse(a: &mut Vec<i32>)
    ensures forall|i: int| 0 <= i < old(a).len() ==> a[i] == old(a)[old(a).len() - 1 - i]
// </vc-spec>
// <vc-code>
{
    let n = a.len();
    let mut i: usize = 0;
    
    while i < n / 2
        invariant
            0 <= i <= n / 2,
            n == a.len(),
            n == old(a).len(),
            // Elements that have been swapped
            forall|k: int| 0 <= k < i ==> a[k] == old(a)[n - 1 - k],
            forall|k: int| 0 <= k < i ==> a[n - 1 - k] == old(a)[k],
            // Elements that haven't been swapped yet
            forall|k: int| i <= k < n - i ==> a[k] == old(a)[k],
        decreases n / 2 - i
    {
        let j = n - 1 - i;
        
        // Read values before swapping to avoid borrow conflicts
        let temp_i = a[i];
        let temp_j = a[j];
        
        // Swap elements at positions i and j
        a.set(i, temp_j);
        a.set(j, temp_i);
        
        i = i + 1;
    }
    
    // Prove the postcondition
    assert forall|k: int| 0 <= k < n implies a[k] == old(a)[n - 1 - k] by {
        if k < n / 2 {
            // This element was swapped in the loop
            assert(a[k] == old(a)[n - 1 - k]);
        } else if k >= n - n / 2 {
            // This element's partner was swapped
            let partner = n - 1 - k;
            assert(partner < n / 2);
            assert(a[k] == old(a)[partner]);
            assert(partner == n - 1 - k);
        } else {
            // For odd-length arrays, the middle element stays in place
            assert(k == n / 2);
            assert(n - 1 - k == k);
            assert(a[k] == old(a)[k]);
        }
    }
}
// </vc-code>

fn main() {
}

}