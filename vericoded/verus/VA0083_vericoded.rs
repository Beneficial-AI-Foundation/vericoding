// <vc-preamble>
use vstd::prelude::*;

verus! {
    spec fn valid_input(n: int) -> bool {
        n >= 1
    }
    
    spec fn min_bills(n: int) -> int
        recommends n >= 1
    {
        n / 100 + (n % 100) / 20 + ((n % 100) % 20) / 10 + (((n % 100) % 20) % 10) / 5 + ((((n % 100) % 20) % 10) % 5)
    }
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): fixed lemma keyword syntax */
fn lemma_min_bills_correct(n: int)
    requires n >= 1
    ensures
        min_bills(n) >= 0,
        min_bills(n) == n / 100 + (n % 100) / 20 + ((n % 100) % 20) / 10 + (((n % 100) % 20) % 10) / 5 + ((((n % 100) % 20) % 10) % 5)
{
}

fn lemma_division_bounds(n: int, d: int)
    requires n >= 0, d > 0
    ensures n / d >= 0
{
}

fn lemma_mod_bounds(n: int, d: int)
    requires n >= 0, d > 0
    ensures 0 <= n % d < d
{
}
// </vc-helpers>

// <vc-spec>
fn solve(n: i8) -> (result: i8)
    requires 
        valid_input(n as int)
    ensures 
        result >= 0,
        result as int == min_bills(n as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): removed proof calls to lemmas which are now functions */
    let hundreds = n / 100;
    let remainder_after_hundreds = n % 100;
    
    let twenties = remainder_after_hundreds / 20;
    let remainder_after_twenties = remainder_after_hundreds % 20;
    
    let tens = remainder_after_twenties / 10;
    let remainder_after_tens = remainder_after_twenties % 10;
    
    let fives = remainder_after_tens / 5;
    let ones = remainder_after_tens % 5;
    
    let total = hundreds + twenties + tens + fives + ones;
    
    total
}
// </vc-code>

}

fn main() {}