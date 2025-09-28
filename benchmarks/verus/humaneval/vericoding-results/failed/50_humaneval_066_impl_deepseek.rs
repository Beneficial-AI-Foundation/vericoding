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

proof fn sum_of_uppercase_ascii_recursion(s: Seq<char>, i: int)
    requires
        0 <= i <= s.len(),
    ensures
        sum_of_uppercase_ascii(s.subrange(0, i)) + (if i < s.len() && ('A' <= s[i] && s[i] <= 'Z') { s[i] as int } else { 0 }) == 
        sum_of_uppercase_ascii(s.subrange(0, i + 1)),
    decreases s.len() - i
{
    if i < s.len() {
        let next_i = i + 1;
        if i == 0 {
            assert(s.subrange(0, 1) == Seq::empty().push(s[0]));
        } else {
            sum_of_uppercase_ascii_recursion(s, next_i);
        }
    }
}

spec fn ascii_uppercase_char(c: char) -> bool {
    'A' <= c && c <= 'Z'
}

proof fn sum_of_uppercase_ascii_nonnegative(s: Seq<char>) 
    ensures
        sum_of_uppercase_ascii(s) >= 0,
    decreases s.len()
{
    if s.len() > 0 {
        let rest = s.subrange(1, s.len() as int);
        sum_of_uppercase_ascii_nonnegative(rest);
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
    /* code modified by LLM (iteration 5): Fixed integer casting to avoid ghost types in exec code */
    let mut total: i32 = 0;
    let mut i: usize = 0;
    
    while i < s.len()
        invariant
            i <= s.len(),
            total == sum_of_uppercase_ascii(s@.subrange(0, i as int)),
            total >= 0,
        decreases s.len() - i
    {
        let c = s[i];
        proof {
            sum_of_uppercase_ascii_recursion(s@, i as int);
        }
        if 'A' <= c && c <= 'Z' {
            total = total + (c as i32);
        }
        i = i + 1;
    }
    
    total
}
// </vc-code>


}

fn main() {}