use vstd::prelude::*;

verus! {

// <vc-helpers>
// No additional helpers needed for this implementation
// </vc-helpers>

// <vc-spec>
fn reverse(a: &mut Vec<i32>)
    ensures forall|k: int| 0 <= k < old(a).len() ==> a[k] == old(a)[old(a).len() as int - 1 - k]
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
            forall|k: int| 0 <= k < i ==> a[k] == old(a)[n as int - 1 - k],
            forall|k: int| n as int - i <= k < n ==> a[k] == old(a)[n as int - 1 - k],
            // Elements that haven't been swapped yet
            forall|k: int| i <= k < n as int - i ==> a[k] == old(a)[k],
        decreases n / 2 - i
    {
        let j = n - 1 - i;
        
        // Store values before swap to avoid borrowing issues
        let temp_i = a[i];
        let temp_j = a[j];
        a.set(i, temp_j);
        a.set(j, temp_i);
        
        i = i + 1;
    }
    
    // After the loop, we need to prove the postcondition holds for all k
    assert forall|k: int| 0 <= k < n implies a[k] == old(a)[n as int - 1 - k] by {
        if k < n / 2 {
            // This case is covered by the first part of the loop invariant
            assert(a[k] == old(a)[n as int - 1 - k]);
        } else {
            // This case is covered by the second part of the loop invariant
            assert(a[k] == old(a)[n as int - 1 - k]);
        }
    }
}
// </vc-code>

fn main() {
}

}