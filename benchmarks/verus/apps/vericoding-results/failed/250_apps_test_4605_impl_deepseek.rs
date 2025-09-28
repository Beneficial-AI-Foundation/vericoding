// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(n: int, a: int, b: int) -> bool {
    n >= 1 && a >= 1 && a <= b && b <= 36
}

spec fn digit_sum(n: int) -> int 
    decreases n
{
    if n <= 0 { 0 }
    else { (n % 10) + digit_sum(n / 10) }
}

spec fn sum_in_range(n: int, a: int, b: int) -> int
    decreases n
{
    if n <= 0 { 0 }
    else if a <= digit_sum(n) && digit_sum(n) <= b { 
        n + sum_in_range(n - 1, a, b) 
    }
    else { 
        sum_in_range(n - 1, a, b) 
    }
}
// </vc-preamble>

// <vc-helpers>
proof fn lemma_digit_sum_i8_equivalent(x: i8)
    ensures
        (x as int >= 0) ==> (digit_sum(x as int) == x as int),
    decreases x as int
{
    if x >= 0 {
        let mut temp = x as int;
        let mut sum = 0;
        
        while temp > 0
            invariant
                temp >= 0,
                sum >= 0,
                sum + digit_sum(temp) == x as int,
            decreases temp
        {
            sum += temp % 10;
            temp = temp / 10;
        }
        
        assert(sum == x as int);
    }
}
// </vc-helpers>

// <vc-spec>
fn solve(n: i8, a: i8, b: i8) -> (result: i8)
    requires valid_input(n as int, a as int, b as int)
    ensures 
        result as int == sum_in_range(n as int, a as int, b as int) &&
        result >= 0
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fix verification errors with proper bounds checking */
    let mut result: i8 = 0;
    let mut current: i32 = n as i32;
    
    while current >= 1
        invariant
            current >= 0,
            result as int == sum_in_range(n as int, a as int, b as int) - sum_in_range(current as int, a as int, b as int),
            result >= 0,
        decreases current
    {
        let mut temp = current;
        let mut sum: i32 = 0;
        
        while temp > 0
            invariant
                temp >= 0,
                sum >= 0,
                sum == digit_sum(current) - digit_sum(temp),
            decreases temp
        {
            sum += temp % 10;
            temp = temp / 10;
        }
        
        assert(sum == digit_sum(current));
        
        if a as i32 <= sum && sum <= b as i32 {
            proof {
                lemma_sum_in_range_recursive_case(current as int, a as int, b as int);
            }
            result = if current <= i8::MAX as i32 {
                result.checked_add(current as i8).unwrap()
            } else {
                result
            };
        }
        current = current - 1;
    }
    
    proof {
        lemma_sum_in_range_base_case(0, a as int, b as int);
    }
    
    result
}
// </vc-code>


}

fn main() {}