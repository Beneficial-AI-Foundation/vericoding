// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(s: Seq<char>) -> bool {
    s.len() >= 1 && s.len() <= 20 && forall|i: int| 0 <= i < s.len() ==> #[trigger] s[i] >= 'a' && #[trigger] s[i] <= 'z'
}

spec fn distinct_strings_count(s: Seq<char>) -> int
    recommends valid_input(s)
{
    s.len() as int * 25 + 26
}

spec fn int_to_string_spec(n: int) -> Seq<char>
    recommends n >= 0
{
    if n == 0 { seq!['0'] }
    else { seq!['0'] } // Simplified for termination
}

spec fn char_of_digit_spec(d: int) -> char
    recommends 0 <= d <= 9
{
    if d == 0 { '0' }
    else if d == 1 { '1' }
    else if d == 2 { '2' }
    else if d == 3 { '3' }
    else if d == 4 { '4' }
    else if d == 5 { '5' }
    else if d == 6 { '6' }
    else if d == 7 { '7' }
    else if d == 8 { '8' }
    else if d == 9 { '9' }
    else { '0' }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): prove int_to_string_spec returns '0' for nonnegative n */
fn int_to_string_spec_is_zero(n: int)
    requires
        n >= 0,
    ensures
        int_to_string_spec(n) == seq!['0'],
{
    proof {
        if n == 0 {
            assert(int_to_string_spec(n) == seq!['0']);
        } else {
            assert(int_to_string_spec(n) == seq!['0']);
        }
    }
}
// </vc-helpers>

// <vc-spec>
fn solve(s: &str) -> (result: String)
    requires valid_input(s@)
    ensures result@ == int_to_string_spec(distinct_strings_count(s@))
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): construct "0" string and prove spec equality */
    let count = distinct_strings_count(s@);
    let result = "0".to_string();
    proof {
        int_to_string_spec_is_zero(count);
        assert(result@ == int_to_string_spec(count));
    }
    result
}
// </vc-code>


}

fn main() {}