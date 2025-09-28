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
{
    let mut idx: usize = 0;
    let mut sum: i32 = 0;
    while idx < s.len()
        invariant
            0 <= idx <= s.len(),
            sum == sum_of_uppercase_ascii(s@.subrange(0, (idx as int))),
        decreases s.len() - idx
    {
        let c = s[idx];
        if 'A' <= c && c <= 'Z' {
            sum = sum + (c as i32);
        }
        idx += 1;
    }
    sum
}
// </vc-code>


}

fn main() {}