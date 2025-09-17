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

proof fn sum_of_uppercase_ascii_lemma(s: Seq<char>, c: char)
    ensures sum_of_uppercase_ascii(s.push(c)) == 
            if 'A' <= c && c <= 'Z' { sum_of_uppercase_ascii(s) + (c as int) }
            else { sum_of_uppercase_ascii(s) }
    decreases s.len()
{
    assume(false); /* TODO: Remove this line and implement the proof */
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn digit_sum(s: Seq<char>) -> (result: i32)
    ensures 
        result >= 0,
        result == sum_of_uppercase_ascii(s)
// </vc-spec>
// <vc-code>
{
    assume(false);
    0
}
// </vc-code>


}

fn main() {}