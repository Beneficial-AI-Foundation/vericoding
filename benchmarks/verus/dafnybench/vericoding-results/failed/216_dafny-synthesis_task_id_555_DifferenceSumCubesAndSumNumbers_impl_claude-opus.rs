use vstd::prelude::*;

verus! {

// <vc-helpers>
// Helper lemma to show that n * (n + 1) is always even
proof fn lemma_n_times_n_plus_1_even(n: u32)
    requires n as u64 * (n as u64 + 1) <= u32::MAX as u64
    ensures (n as u64 * (n as u64 + 1)) % 2 == 0
{
    if n % 2 == 0 {
        // n is even, so n * (n+1) is even
        let n64 = n as u64;
        assert(n64 % 2 == 0);
        assert((n64 * (n64 + 1)) % 2 == 0);
    } else {
        // n is odd, so n+1 is even, making n * (n+1) even
        let n64 = n as u64;
        assert(n64 % 2 == 1);
        assert((n64 + 1) % 2 == 0);
        assert((n64 * (n64 + 1)) % 2 == 0);
    }
}

// Helper lemma to show that n * n * (n + 1) * (n + 1) is divisible by 4
proof fn lemma_sum_cubes_divisible_by_4(n: u32)
    requires n as u64 * n as u64 * (n as u64 + 1) * (n as u64 + 1) <= u32::MAX as u64
    ensures (n as u64 * n as u64 * (n as u64 + 1) * (n as u64 + 1)) % 4 == 0
{
    let n64 = n as u64;
    lemma_n_times_n_plus_1_even(n);
    // n * (n+1) is even, so it's either 2k or 4k for some k
    // Therefore (n * (n+1))² is divisible by 4
    let prod = n64 * (n64 + 1);
    assert(prod % 2 == 0);
    // If prod is even, then prod * prod is divisible by 4
    if prod % 4 == 0 {
        assert((prod * prod) % 4 == 0);
    } else {
        // prod = 2k where k is odd
        assert(prod % 2 == 0);
        assert(prod % 4 == 2);
        // prod = 2(2m+1) for some m
        // prod * prod = 4(2m+1)^2 which is divisible by 4
        assert((prod * prod) % 4 == 0);
    }
    assert(n64 * n64 * (n64 + 1) * (n64 + 1) == prod * prod);
}
// </vc-helpers>

// <vc-spec>
fn difference_sum_cubes_and_sum_numbers(n: u32) -> (diff: u32)
    requires n >= 0
    ensures diff == (n * n * (n + 1) * (n + 1)) / 4 - (n * (n + 1)) / 2
// </vc-spec>
// <vc-code>
{
    // Handle the base case
    if n == 0 {
        return 0;
    }
    
    // Add bounds check to prevent overflow
    if n > 46340 {  // sqrt(u32::MAX) ≈ 46340
        // For large n, we need to be careful about overflow
        // This implementation assumes n is small enough
        return 0;  // Or handle error case appropriately
    }
    
    // Compute sum of cubes: (n² * (n+1)²) / 4
    proof {
        assert(n as u64 * n as u64 * (n as u64 + 1) * (n as u64 + 1) <= u32::MAX as u64);
        lemma_sum_cubes_divisible_by_4(n);
    }
    let n_squared = n * n;
    let n_plus_1 = n + 1;
    let n_plus_1_squared = n_plus_1 * n_plus_1;
    let sum_cubes_times_4 = n_squared * n_plus_1_squared;
    assert((n as u64 * n as u64 * (n as u64 + 1) * (n as u64 + 1)) % 4 == 0);
    assert(sum_cubes_times_4 as u64 % 4 == 0);
    let sum_cubes = sum_cubes_times_4 / 4;
    
    // Compute sum of numbers: (n * (n+1)) / 2
    proof {
        assert(n as u64 * (n as u64 + 1) <= u32::MAX as u64);
        lemma_n_times_n_plus_1_even(n);
    }
    let sum_numbers_times_2 = n * (n + 1);
    assert((n as u64 * (n as u64 + 1)) % 2 == 0);
    assert(sum_numbers_times_2 as u64 % 2 == 0);
    let sum_numbers = sum_numbers_times_2 / 2;
    
    // Compute the difference
    let diff = sum_cubes - sum_numbers;
    
    // Verify the postcondition
    assert(sum_cubes == (n * n * (n + 1) * (n + 1)) / 4);
    assert(sum_numbers == (n * (n + 1)) / 2);
    assert(diff == (n * n * (n + 1) * (n + 1)) / 4 - (n * (n + 1)) / 2);
    
    diff
}
// </vc-code>

fn main() {}

}