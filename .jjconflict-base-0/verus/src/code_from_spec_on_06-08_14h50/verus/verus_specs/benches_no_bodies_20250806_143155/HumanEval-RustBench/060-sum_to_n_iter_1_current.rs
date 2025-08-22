use vstd::prelude::*;

verus! {

spec fn spec_sum_to_n(n: nat) -> (ret:nat)
    decreases n,
{
    if (n == 0) {
        0
    } else {
        n + spec_sum_to_n((n - 1) as nat)
    }
}
// pure-end

fn sum_to_n(n: u32) -> (sum: Option<u32>)
    // post-conditions-start
    ensures
        sum.is_some() ==> sum.unwrap() == spec_sum_to_n(n as nat),
    // post-conditions-end
{
    // Check for overflow: n * (n + 1) / 2 must fit in u32
    // This happens when n * (n + 1) <= 2^32 * 2 = 2^33
    // We can check this by seeing if n <= sqrt(2^33) ≈ 92681
    // But more precisely, we check if the multiplication would overflow
    
    if n > 65535 { // Conservative bound to avoid overflow in intermediate calculations
        return None;
    }
    
    let n_u64 = n as u64;
    let product = n_u64 * (n_u64 + 1);
    let result = product / 2;
    
    if result > u32::MAX as u64 {
        None
    } else {
        Some(result as u32)
    }
}

}
fn main() {}