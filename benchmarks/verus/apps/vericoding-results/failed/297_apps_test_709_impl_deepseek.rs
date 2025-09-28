// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn count_ones_in_binary(n: int) -> int
    recommends n >= 1
    decreases n
    when n >= 1
{
    if n == 1 {
        1
    } else if n % 2 == 1 {
        1 + count_ones_in_binary(n / 2)
    } else {
        count_ones_in_binary(n / 2)
    }
}

spec fn valid_input(x: int) -> bool {
    x >= 1
}

spec fn valid_output(x: int, result: int) -> bool {
    valid_input(x) && result == count_ones_in_binary(x)
}
// </vc-preamble>

// <vc-helpers>
proof fn lemma_count_ones_next(n: int)
    requires n >= 1,
    ensures 
        if n % 2 == 1 {
            count_ones_in_binary(n) == 1 + count_ones_in_binary(n / 2)
        } else {
            count_ones_in_binary(n) == count_ones_in_binary(n / 2)
        }
    decreases n
{
    if n == 1 {
    } else {
        lemma_div_2_decreases(n);
        lemma_count_ones_range(n / 2);
    }
}
// </vc-helpers>

// <vc-spec>
fn min_bacteria(x: i8) -> (result: i8)
    requires valid_input(x as int)
    ensures valid_output(x as int, result as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed postcondition and assertion */
    let mut count: i8 = 0;
    let mut current = x;
    
    proof {
        lemma_count_ones_range(x as int);
    }
    
    while current > 0
        invariant 
            current >= 0,
            count as int + count_ones_in_binary(current as int) == count_ones_in_binary(x as int),
            count >= 0
        decreases current as int
    {
        proof {
            lemma_div_2_decreases(current as int);
            lemma_count_ones_next(current as int);
        }
        
        if current % 2 == 1 {
            assert(count < i8::MAX);
            count = count + 1;
        }
        
        current = current / 2;
        
        proof {
            assert(current >= 0);
        }
    }
    
    proof {
        assert(current == 0);
        assert(count_ones_in_binary(0) == 0);
    }
    
    count
}
// </vc-code>


}

fn main() {}