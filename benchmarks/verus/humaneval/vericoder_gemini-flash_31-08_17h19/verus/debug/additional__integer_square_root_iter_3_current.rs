use vstd::prelude::*;

verus! {

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn integer_square_root(n: i32) -> (result: i32)
    // pre-conditions-start
    requires
        n >= 1,
    // pre-conditions-end
    // post-conditions-start
    ensures
        0 <= result * result,
        result * result <= n,
        n < (result + 1) * (result + 1)
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    // impl-start
    let mut low: u32 = 0;
    let mut high: u32 = n as u32;
    let mut ans: u32 = 0;

    while low <= high
        invariant
            low >= 0,
            high <= n as u32,
            ans * ans <= n as u32,
            ans <= low, // ans is the largest mid seen so far, and low is always at least ans
            high + 1 >= low, // search space [low, high] is valid
            n >= 1, // from precondition
            // Maintain that the square root is within the search range [ans, high] potentially
            ans * ans <= n as u32,
            forall|x: u32| ans <= x && x <= high ==> x * x >= ans * ans,
        decreases high - low
    {
        let mid: u32 = low + (high - low) / 2;

        if mid > n as u32 / mid
            && mid > 0 // Ensure mid is not zero to avoid division by zero.
        {
            high = mid - 1;
            // Proof: if mid > n/mid then mid*mid > n. Thus, mid cannot be the square root.
            assert(mid * mid > n as u32);
        } else {
            ans = mid;
            low = mid + 1;
            // Proof: if mid <= n/mid then mid*mid <= n. mid is a candidate for the sqrt.
            assert(mid * mid <= n as u32);
        }
    }
    ans as i32
    // impl-end
}
// </vc-code>

fn main() {}
}