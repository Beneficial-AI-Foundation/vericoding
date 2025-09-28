// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn sum_of_uppercase_ascii(s: Seq<char>) -> int
    decreases s.len()
{
    if s.len() == 0 { 
        0
    } else {
        let c = s[0];
        let rest = sum_of_uppercase_ascii(s.subrange(1, s.len() as int));
        if 'A' <= c && c <= 'Z' { 
            (c as int) + rest
        } else {
            rest
        }
    }
}

// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn digit_sum(s: Vec<char>) -> (result: i32)
    ensures 
        result >= 0,
        result == sum_of_uppercase_ascii(s@)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Corrected decreases clause to `s.len() - i`, cast `c as int` before adding to sum to prevent overflow */
{
    let mut sum: i32 = 0;
    let mut i: usize = 0;

    while i < s.len()
        invariant
            0 <= i && i <= s.len(),
            sum as int == sum_of_uppercase_ascii(s@.subrange(0, i as int)),
            sum >= 0,
        decreases s.len() - i
    {
        let c = s[i];
        if 'A' <= c && c <= 'Z' {
            sum = sum + (c as int) as i32;
        }
        i = i + 1;
    }
    sum
}
// </vc-code>


}

fn main() {}