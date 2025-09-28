use vstd::prelude::*;

verus! {

/**
  Inverts an array of ints.
 */

// <vc-helpers>
// No additional helpers needed for this implementation
// </vc-helpers>

// <vc-spec>
fn invert_array(a: &mut Vec<i32>)
    ensures
        a.len() == old(a).len(),
        forall|i: int| 0 <= i < a.len() ==> a[i] == old(a)[a.len() - 1 - i],
// </vc-spec>
// <vc-code>
{
    let n = a.len();
    let mut i: usize = 0;
    
    while i < n / 2
        invariant
            a.len() == n,
            n == old(a).len(),
            0 <= i <= n / 2,
            // Elements before i have been swapped with their corresponding elements
            forall|j: int| 0 <= j < i ==> #[trigger] a@[j] == old(a)@[n as int - 1 - j],
            forall|j: int| 0 <= j < i ==> #[trigger] a@[n as int - 1 - j] == old(a)@[j],
            // Elements in the middle (between i and n-1-i) haven't been touched yet
            forall|j: int| i <= j && j < n as int - i ==> #[trigger] a@[j] == old(a)@[j],
        decreases n / 2 - i
    {
        let j = n - 1 - i;
        
        // Swap a[i] and a[j]
        let temp = a[i];
        let temp2 = a[j];
        a.set(i, temp2);
        a.set(j, temp);
        
        i = i + 1;
    }
    
    // After the loop, verify the postcondition
    assert forall|k: int| 0 <= k < n implies a@[k] == old(a)@[n as int - 1 - k] by {
        if k < n as int / 2 {
            // These were swapped in the loop
            assert(a@[k] == old(a)@[n as int - 1 - k]);
        } else if k >= n as int - n as int / 2 {
            // These were also swapped (as the other half of the pairs)
            let paired_idx = n as int - 1 - k;
            assert(0 <= paired_idx < n as int / 2);
            assert(a@[n as int - 1 - paired_idx] == old(a)@[paired_idx]);
            assert(n as int - 1 - paired_idx == k);
            assert(a@[k] == old(a)@[n as int - 1 - k]);
        } else {
            // Middle element (only exists if n is odd)
            assert(n as int % 2 == 1);
            assert(k == n as int / 2);
            assert(n as int - 1 - k == k);
            assert(a@[k] == old(a)@[k]);
            assert(a@[k] == old(a)@[n as int - 1 - k]);
        }
    }
}
// </vc-code>

fn main() {
}

}