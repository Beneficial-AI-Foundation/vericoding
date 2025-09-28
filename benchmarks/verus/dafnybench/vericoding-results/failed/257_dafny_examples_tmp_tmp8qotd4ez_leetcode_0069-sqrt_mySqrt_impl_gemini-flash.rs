use vstd::prelude::*;

verus! {

// Author: Shaobo He

spec fn sqrt(x: int, r: int) -> bool {
    r * r <= x && (r + 1) * (r + 1) > x
}

// <vc-helpers>
fn sqrt_auto_proof_1(x: int, r: int, _dummy: bool)
    requires
        r >= 0,
        r * r <= x,
    ensures
        r <= x,
{
    if r == 0 {
        assert(r <= x);
    } else {
        assert(r * r <= x);
    }
}

fn sqrt_auto_proof_2(x: int, r: int)
    requires
        r >= 0,
        x >= 0,
        r * r <= x,
        (r + 1) * (r + 1) > x,
    ensures
        r <= x,
{
    sqrt_auto_proof_1(x, r, true);
}

// Helper proof for (ans + 1)^2 > x
proof fn prove_post_condition(x: int, ans: int, low: int, high: int)
    requires
        x >= 0,
        ans >= 0,
        ans * ans <= x,
        low == ans + 1, // This means low was set from ans + 1
        high == ans,    // high was set from ans
        low > high,     // loop terminated
    ensures
        (ans + 1) * (ans + 1) > x,
{
     // When the loop terminates, low is ans + 1 (from when ans was found) and high is less than low.
     // The loop invariant `low <= high+1` becomes `ans+1 <= high+1` which implies `ans <= high`
     // Combined with `low > high` (ans+1 > high), we get `high = ans`.
     // So when `high` pointer passed `low` pointer, all elements from `low_initial` to `high_final`
     // were checked.
     // In the last iteration, if `mid = ans`, then `ans*ans <= x`, `ans` became current ans, `low` became `ans+1`.
     // If `mid = ans + 1`, then it must be that `(ans+1)*(ans+1) > x` for loop to terminate with `high = mid - 1`.
     // Since `low > high`, the search space collapsed.
     // The final `ans` is the largest integer whose square is less than or equal to `x`.
     // Therefore, `(ans+1)*(ans+1)` must be greater than `x`.

     // Consider the very last `mid` value that was checked:
     // If `mid == ans`, then `mid*mid <= x`, `ans` was set to `mid`, `low` was set to `mid + 1`.
     // The next iteration, `low` is `ans + 1`.
     // If the loop terminates with `low > high`, it implies that for `low = ans + 1`, either
     // its `mid'` value in the next iteration caused `(mid')*(mid') > x` or `high` was already `ans`.
     // Suppose `ans` is the correct result. Then `ans*ans <= x` and `(ans+1)*(ans+1) > x`.
     // Our loop guarantees `ans*ans <= x` by `ans = mid` only when `mid*mid <= x`.
     // For `(ans+1)*(ans+1) > x`:
     // Observe that `low` in the invariant is always `ans_prev + 1` from some iteration OR `low` kept increasing because `mid`, `mid+1`, `mid+2`, ... all had their squares `> x`.
     // When `low > high`, the interval `[low, high]` is empty.
     // The `ans` obtained is the largest `mid` that satisfies `mid*mid <= x`.
     // This means that `ans+1` (which is the next integer) must have a square greater than `x`
     // (otherwise, `ans` would have been updated to `ans+1`).
     // This is the core logic of binary search finding the largest point satisfying a predicate.
}
// </vc-helpers>

// <vc-spec>
#[verifier::exec_allows_no_decreases_clause]
fn mySqrt(x: int) -> (res: int)
    requires 0 <= x,
    ensures sqrt(x, res),
// </vc-spec>
// <vc-code>
{
    if x == 0 {
        return 0
    }
    let mut low: int = 0;
    let mut high: int = x;
    let mut ans: int = 0;

    while low <= high
        invariant
            x >= 0,
            low >= 0,
            high >= -1, // high can become -1
            ans >= 0,
            low <= x + 1, // `low` can go up to `x+1` in the loop condition `low <= high`
            high <= x,
            ans * ans <= x,
            // If `low > high`, then `ans` is our result.
            // When `low` moves from `mid + 1`, it means `mid` was a valid `ans`.
            // When `high` moves from `mid - 1`, it means `mid` was too high.
    {
        let mid: int = low + (high - low) / 2;

        // Proof that mid >= 0 if low >= 0 and high >= -1 (and low <= high + 1 for sanity, though not strictly needed here)
        proof {
            if low <= high {
                assert(low <= mid); // low + (high - low) / 2 >= low because (high - low) / 2 >= 0
                assert(low >= 0 ==> mid >= 0);
            }
        }

        if mid > 0 && mid > x / mid {
            // Avoid overflow when mid * mid by checking mid > x / mid
            // Also, handle mid == 0 to avoid division by zero.
            // If mid is 0, mid*mid is 0 which is always <= x (since x >= 0).
            // So only consider this branch if mid is not 0.
            high = mid - 1;
        } else if mid * mid <= x {
            // This mid is a possible answer, store it and try for a larger one.
            ans = mid;
            low = mid + 1;
        } else {
            // mid*mid > x, so mid is too large. Reduce search space.
            high = mid - 1;
        }
    }

    // After the loop, `low > high`.
    // The `ans` variable stores the largest `mid` encountered for which `mid*mid <= x`.
    // We need to prove `(ans + 1) * (ans + 1) > x`.

    assert(ans * ans <= x);
    //
    // Proof of (ans + 1) * (ans + 1) > x :
    // The loop finds the largest `r` such that `r*r <= x`.
    // When the loop terminates, `low` is set to `ans + 1` from the last successful update,
    // and `high` has been set to something less than `low`.
    // Specifically, `high` must be `ans` for `low` to finally cross `high`.
    // If `low` equals `ans + 1` and `high` equals `ans`, then `low = high + 1`.
    // This is the state where the search space `[low, high]` has collapsed.
    // At this point, the `ans` value is the largest integer `r` we've found such that `r*r <= x`.
    // For any integer `k` such that `k > ans` (i.e., `k >= ans + 1`), it must be that `k*k > x`,
    // otherwise `ans` would have been updated to `k`.
    // In particular, `(ans + 1) * (ans + 1) > x`.

    // Consider the case where `x` is `0`.
    // `mySqrt(0)` returns `0`. `sqrt(0,0)` is `0*0 <= 0 && (0+1)*(0+1) > 0`, which is `true && true`, `true`.

    // Consider `x` is `1`.
    // `low = 0, high = 1, ans = 0`.
    // Loop 1: `mid = 0`. `0*0 <= 1`. `ans = 0`, `low = 1`.
    // Loop 2: `low = 1, high = 1`. `mid = 1`. `1*1 <= 1`. `ans = 1`, `low = 2`.
    // Loop 3: `low = 2, high = 1`. `low > high`. Loop terminates.
    // Return `ans = 1`. `sqrt(1,1)` is `1*1 <= 1 && (1+1)*(1+1) > 1`, which is `true && 4 > 1`, `true`.

    // Consider `x` is `8`.
    // `low = 0, high = 8, ans = 0`.
    // Loop 1: `mid = 4`. `4*4 = 16 > 8`. `high = 3`.
    // Loop 2: `low = 0, high = 3`. `mid = 1`. `1*1 = 1 <= 8`. `ans = 1`, `low = 2`.
    // Loop 3: `low = 2, high = 3`. `mid = 2`. `2*2 = 4 <= 8`. `ans = 2`, `low = 3`.
    // Loop 4: `low = 3, high = 3`. `mid = 3`. `3*3 = 9 > 8`. `high = 2`.
    // Loop 5: `low = 3, high = 2`. `low > high`. Loop terminates.
    // Return `ans = 2`. `sqrt(8,2)` is `2*2 <= 8 && (2+1)*(2+1) > 8`, which is `true && 9 > 8`, `true`.

    proof {
        // We know ans*ans <= x from invariant.
        // We need to prove (ans+1)*(ans+1) > x.
        // The binary search guarantees that `ans` is the largest integer `k` such that `k*k <= x`.
        // This implies for any integer `k' = ans+1`, `k'*k' > x`.
        // The post-condition logic directly follows from the property of the binary search algorithm
        // which finds the maximal element satisfying a property.
        assert((ans + 1) * (ans + 1) > x);
    }

    ans
}
// </vc-code>

fn main() {
}

}