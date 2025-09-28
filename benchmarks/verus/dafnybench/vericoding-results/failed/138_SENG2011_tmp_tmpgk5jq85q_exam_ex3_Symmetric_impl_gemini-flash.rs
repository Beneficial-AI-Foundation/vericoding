use vstd::prelude::*;

verus! {

// <vc-helpers>
#[verifier(external_body)]
#[cfg(test)]
pub fn symmetric_test_case(a: &[i32], expected: bool) {
    let result = symmetric(a);
    assert_eq!(result, expected);
}
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
    if n == 0 {
        return true;
    }

    let mut i: nat = 0;
    while (i as int) < (n as int) / 2
        invariant
            0 <= i as int,
            i as int <= (n as int) / 2, // Corrected upper bound for `i`
            forall|j: int| 0 <= j && j < i as int ==> #[trigger] a[j as nat] == a[(n - j - 1) as nat],
        decreases (n as int) / 2 - (i as int)
    {
        proof {
            // Proof that n - i - 1 is a valid index.
            // Since i < n/2, then 2*i < n.
            // So, 2*i <= n-1 (if n is odd, 2*i <= n-1, if n is even, 2*i <= n-2)
            // n - i - 1 >= n - (n/2 - 1) - 1  (if n/2 is integer)
            // n - i - 1 >= n/2 >= 0
            // More formally:
            // i < n/2 implies 2*i < n.
            // If n is even, n = 2k. i < k. So i <= k-1.
            // n-i-1 = 2k - i - 1 >= 2k - (k-1) - 1 = k >= 0.
            // If n is odd, n = 2k+1. i <= k.
            // n-i-1 = 2k+1 - i - 1 >= 2k+1 - k - 1 = k >= 0.
            assert((n as int) - (i as int) - 1 >= 0) by(nonlinear_arith);
        }
        if a[i as usize] != a[(n - i - 1) as usize] {
            return false;
        }
        i = i + 1;
    }
    true
}
// </vc-code>

fn main() {}

}