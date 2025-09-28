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
proof fn sum_of_uppercase_ascii_nonnegative(s: Seq<char>)
    ensures
        sum_of_uppercase_ascii(s) >= 0,
    decreases s.len()
{
    if s.len() == 0 {
    } else {
        let c = s[0];
        sum_of_uppercase_ascii_nonnegative(s.subrange(1, s.len() as int));
        if 'A' <= c && c <= 'Z' {
            assert((c as int) >= 0);
        }
    }
}

// </vc-helpers>

// <vc-spec>
fn digit_sum(s: Vec<char>) -> (result: i32)
    ensures 
        result >= 0,
        result == sum_of_uppercase_ascii(s@)
// </vc-spec>
// <vc-code>
{
    let mut i: int = 0;
    let mut result: i32 = 0;
    while i < s.len() as int
        invariant
            0 <= i,
            i <= s.len() as int,
            result >= 0,
        decreases (s.len() as int) - i
    {
        let c = s[i as usize];
        if 'A' <= c && c <= 'Z' {
            result = result + (c as i32);
        }
        i = i + 1;
    }
    result
}
// </vc-code>


}

fn main() {}