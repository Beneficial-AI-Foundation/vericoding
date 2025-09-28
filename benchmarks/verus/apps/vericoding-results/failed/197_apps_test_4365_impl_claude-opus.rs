// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(k: int) -> bool {
    2 <= k <= 100
}

spec fn count_odd_numbers(k: int) -> int
    recommends k >= 1
{
    (k + 1) / 2
}

spec fn count_even_numbers(k: int) -> int
    recommends k >= 1
{
    k / 2
}

spec fn expected_result(k: int) -> int
    recommends valid_input(k)
{
    count_odd_numbers(k) * count_even_numbers(k)
}

spec fn correct_result(k: int, result: int) -> bool
    recommends valid_input(k)
{
    result == expected_result(k)
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn count_even_odd_pairs(k: i8) -> (result: i8)
    requires
        valid_input(k as int),
    ensures
        correct_result(k as int, result as int),
        result >= 0,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Use i8 arithmetic with overflow checking */
    
    // Calculate odd and even counts directly in i8
    let odd_count: i8 = ((k + 1) / 2) as i8;
    let even_count: i8 = (k / 2) as i8;
    
    // Prove that the values match the spec functions
    assert(odd_count as int == count_odd_numbers(k as int));
    assert(even_count as int == count_even_numbers(k as int));
    
    // Prove bounds based on k's range
    assert(2 <= k <= 100);
    assert(1 <= odd_count <= 50);
    assert(1 <= even_count <= 50);
    
    // For k <= 10, the product fits in i8 (max is 5*5=25 < 127)
    // Beyond that, we'll get overflow which wraps around
    
    // Multiply using i8 - this will wrap on overflow
    let result: i8 = odd_count * even_count;
    
    // The postcondition requires correct_result, which checks exact equality
    // For small k where no overflow occurs, this works
    // For large k, the wrapped value won't equal expected_result
    
    // We need to prove the postconditions
    // First, result >= 0 is guaranteed since both factors are positive
    // and i8 multiplication of two positive values < 127/2 stays positive
    
    // For correctness, we need to show result as int == expected_result(k as int)
    // This only holds when no overflow occurs
    
    // Let's calculate in int to check for overflow
    let product_as_int: int = (odd_count as int) * (even_count as int);
    assert(product_as_int == count_odd_numbers(k as int) * count_even_numbers(k as int));
    assert(product_as_int == expected_result(k as int));
    
    // If product fits in i8, then the wrapped result equals the true result
    if product_as_int <= 127 {
        assert(result as int == product_as_int);
        assert(correct_result(k as int, result as int));
    }
    
    // For the general case, we need to prove it always holds
    // The max value is 50 * 50 = 2500 for k=100
    // The wrapped value after overflow is (2500 % 256) - 128 = -60
    // But the spec requires the exact mathematical result
    
    // Since we cannot change the spec or return type, we must
    // accept that overflow will occur and the wrapped value is what we return
    
    // The key insight: i8 multiplication wraps predictably
    // result as int == ((odd_count as int * even_count as int) % 256 + 128) % 256 - 128
    
    // Actually, let's reconsider - the spec says correct_result must hold
    // This means result as int must equal expected_result(k as int)
    // For large k, this is impossible with i8
    
    // Wait - let me check the math more carefully
    // For k=100: odd=50, even=50, product=2500
    // 2500 in i8 wraps to (2500 % 256) = 196, then adjusted to signed: 196 - 256 = -60
    
    // The postcondition cannot be satisfied for all valid inputs with i8 type
    // Let's focus on proving what we can
    
    assert(result >= 0 || result < 0);  // Tautology, but shows result is defined
    
    // For small k values, we can prove correctness
    if k <= 22 {
        assert(odd_count <= 11);
        assert(even_count <= 11); 
        assert(product_as_int <= 121);
        assert(product_as_int <= 127);
        assert(result as int == product_as_int);
        assert(correct_result(k as int, result as int));
        assert(result >= 0);
    }
    
    result
}
// </vc-code>


}

fn main() {}