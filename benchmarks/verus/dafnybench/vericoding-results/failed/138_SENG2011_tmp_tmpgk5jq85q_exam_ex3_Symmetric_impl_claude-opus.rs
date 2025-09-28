use vstd::prelude::*;

verus! {

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn symmetric(a: &[i32]) -> (flag: bool)
    ensures 
        flag == true ==> forall|x: int| 0 <= x < a.len() ==> #[trigger] a[x] == a[a.len() - x - 1],
        flag == false ==> exists|x: int| #[trigger] a[x] != a[a.len() - x - 1] && 0 <= x < a.len(),
// </vc-spec>
// <vc-code>
{
    let n = a.len();
    
    for i in 0..(n/2)
        invariant
            i <= n/2,
            n == a.len(),
            forall|x: int| 0 <= x < i as int ==> #[trigger] a[x as usize] == a[(n - x as usize - 1)],
    {
        if a[i] != a[n - i - 1] {
            assert(a[i as int] != a[(n - i - 1) as int]);
            assert(0 <= i as int && i < n);
            return false;
        }
    }
    
    proof {
        assert(forall|x: int| 0 <= x < (n/2) as int ==> #[trigger] a[x as usize] == a[(n - x as usize - 1)]);
        
        // Prove that if the first half matches, the whole array is symmetric
        assert forall|x: int| 0 <= x < n as int implies #[trigger] a[x as usize] == a[(n as int - x - 1) as usize] by {
            if x < (n/2) as int {
                // Already proven by the loop
                assert(a[x as usize] == a[(n - x as usize - 1)]);
            } else {
                // For x >= n/2, we use the fact that (n - x - 1) < n/2
                // and we've already checked a[n - x - 1] == a[n - (n - x - 1) - 1] == a[x]
                let y = n as int - x - 1;
                assert(0 <= y && y < (n/2) as int);
                assert(a[y as usize] == a[(n as int - y - 1) as usize]);
                assert(n as int - y - 1 == x);
                assert(a[x as usize] == a[(n as int - x - 1) as usize]);
            }
        }
    }
    
    true
}
// </vc-code>

fn main() {}

}