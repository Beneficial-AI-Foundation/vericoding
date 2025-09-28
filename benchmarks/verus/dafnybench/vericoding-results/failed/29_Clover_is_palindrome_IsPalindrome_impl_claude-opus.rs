use vstd::prelude::*;

verus! {

// <vc-helpers>
// No additional helpers needed for this implementation
// </vc-helpers>

// <vc-spec>
fn is_palindrome(x: Seq<char>) -> (result: bool)
  ensures result <==> (forall|i: int| 0 <= i < x.len() ==> #[trigger] x[i] == x[x.len() - i - 1])
// </vc-spec>
// <vc-code>
{
    let n = x.len();
    
    if n == 0 {
        return true;
    }
    
    let mut i: usize = 0;
    
    while i < n / 2
        invariant
            0 <= i <= n / 2,
            n == x.len(),
            forall|j: int| 0 <= j < i as int ==> #[trigger] x[j] == x[n as int - j - 1],
    {
        if x[i as int] != x[n as int - i as int - 1] {
            // Found a mismatch, so it's not a palindrome
            assert(!(x[i as int] == x[n as int - i as int - 1]));
            assert(0 <= i as int);
            assert(i as int < n);
            assert(!(forall|k: int| 0 <= k < n ==> #[trigger] x[k] == x[n as int - k - 1]));
            return false;
        }
        i = i + 1;
    }
    
    // We've checked all pairs up to the middle
    assert(i == n / 2);
    assert(forall|j: int| 0 <= j < (n / 2) as int ==> #[trigger] x[j] == x[n as int - j - 1]);
    
    // Prove that if the first half matches, then all positions match
    assert forall|k: int| 0 <= k < n implies #[trigger] x[k] == x[n as int - k - 1] by {
        if k < (n / 2) as int {
            // Already proved in the loop invariant
            assert(x[k] == x[n as int - k - 1]);
        } else {
            // For k >= n/2, we use symmetry
            let k_mirror = n as int - k - 1;
            assert(0 <= k_mirror);
            assert(k_mirror < n);
            assert(k_mirror < (n / 2) as int);
            assert(x[k_mirror] == x[n as int - k_mirror - 1]);
            assert(n as int - k_mirror - 1 == k);
            assert(x[k_mirror] == x[k]);
            assert(x[k] == x[k_mirror]);
            assert(x[k] == x[n as int - k - 1]);
        }
    }
    
    true
}
// </vc-code>

fn main() {}

}