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
/* helper modified by LLM (iteration 5): predicate for uppercase */
spec fn is_upper(c: char) -> bool {
    'A' <= c && c <= 'Z'
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
    /* code modified by LLM (iteration 5): iterate with runtime i32/usize and ghost int accumulator to match spec */
    let mut acc: i32 = 0;
    let mut idx: usize = 0;
    let mut ghost acc_spec: int = 0;
    while idx < s.len()
        invariant
            acc as int == acc_spec,
            acc_spec == sum_of_uppercase_ascii(s@.subrange(0, idx as int)),
            idx <= s.len(),
        decreases
            s.len() - idx
    {
        let c = s[idx];
        if 'A' <= c && c <= 'Z' {
            acc = acc + (c as i32);
            acc_spec = acc_spec + (c as int);
        }
        idx = idx + 1;
    }
    acc
}
// </vc-code>


}

fn main() {}