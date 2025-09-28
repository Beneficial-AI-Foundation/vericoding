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
/* helper modified by LLM (iteration 5): fixed integer literals to use explicit int casting */
fn lemma_count_ones_positive(n: int)
    requires n >= 1
    ensures count_ones_in_binary(n) >= 1
    decreases n
{
    if n == 1int {
        // base case: count_ones_in_binary(1) == 1
    } else if n % 2int == 1int {
        // n is odd, so n >= 3, and n/2 >= 1
        lemma_count_ones_positive(n / 2int);
    } else {
        // n is even and >= 2, so n/2 >= 1
        lemma_count_ones_positive(n / 2int);
    }
}

fn lemma_count_ones_bounded(n: int)
    requires n >= 1
    ensures count_ones_in_binary(n) <= 64
    decreases n
{
    if n == 1int {
        // base case
    } else if n % 2int == 1int {
        lemma_count_ones_bounded(n / 2int);
    } else {
        lemma_count_ones_bounded(n / 2int);
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
    /* code modified by LLM (iteration 5): fixed integer literals to use explicit int casting */
    let mut current = x;
    let mut count = 0i8;
    
    proof {
        lemma_count_ones_positive(x as int);
        lemma_count_ones_bounded(x as int);
    }
    
    while current > 0
        invariant
            current >= 0,
            count >= 0,
            count <= 64,
            count + count_ones_in_binary(current as int) == count_ones_in_binary(x as int),
        decreases current
    {
        if current % 2 == 1 {
            count = count + 1;
        }
        current = current / 2;
    }
    
    count
}
// </vc-code>


}

fn main() {}