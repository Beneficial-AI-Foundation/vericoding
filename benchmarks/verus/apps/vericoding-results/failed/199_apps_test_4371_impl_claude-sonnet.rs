// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(s: Seq<char>) -> bool {
    s.len() >= 3 && forall|i: int| 0 <= i < s.len() ==> #[trigger] s.index(i) >= '1' && #[trigger] s.index(i) <= '9'
}

spec fn string_to_int(s: Seq<char>) -> int {
    100 * ((s.index(0) as int) - ('0' as int)) + 
    10 * ((s.index(1) as int) - ('0' as int)) + 
    ((s.index(2) as int) - ('0' as int))
}

spec fn abs_diff(x: int) -> int {
    if x >= 0 { x } else { -x }
}

spec fn substring_at_index(s: Seq<char>, i: int) -> Seq<char> {
    s.subrange(i, i + 3)
}

spec fn is_minimum_difference(s: Seq<char>, result: int) -> bool {
    valid_input(s) ==> (
        result >= 0 &&
        (exists|i: int| 0 <= i <= s.len() - 3 && result == abs_diff(753 - string_to_int(#[trigger] substring_at_index(s, i)))) &&
        (forall|i: int| 0 <= i <= s.len() - 3 ==> result <= abs_diff(753 - string_to_int(#[trigger] substring_at_index(s, i))))
    )
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): removed invalid proof block returning value */
fn char_to_digit_ghost(c: char) -> (result: int)
    requires c >= '1' && c <= '9'
    ensures result == (c as int) - ('0' as int)
{
    (c as int) - ('0' as int)
}

fn char_to_digit(c: char) -> (result: u32)
    requires c >= '1' && c <= '9'
    ensures result == ((c as u8) - ('0' as u8)) as u32
{
    ((c as u8) - ('0' as u8)) as u32
}

fn compute_number(a: char, b: char, c: char) -> (result: u32)
    requires a >= '1' && a <= '9',
             b >= '1' && b <= '9',
             c >= '1' && c <= '9'
    ensures result == 100 * char_to_digit(a) + 10 * char_to_digit(b) + char_to_digit(c)
{
    100 * char_to_digit(a) + 10 * char_to_digit(b) + char_to_digit(c)
}

fn abs_difference(x: i32) -> (result: i32)
    ensures result >= 0
{
    if x >= 0 { x } else { -x }
}
// </vc-helpers>

// <vc-spec>
fn solve(s: Vec<char>) -> (result: i32)
    requires valid_input(s@)
    ensures is_minimum_difference(s@, result as int)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): using u32/i32 types for executable code with proper ghost arithmetic */
{
    let mut min_diff = i32::MAX;
    let mut i = 0;
    
    while i <= s.len() - 3
        invariant
            0 <= i <= s.len() - 3 + 1,
            min_diff >= 0
    {
        let num = compute_number(s[i], s[i + 1], s[i + 2]);
        let diff = abs_difference(753 - (num as i32));
        
        if diff < min_diff {
            min_diff = diff;
        }
        
        i += 1;
    }
    
    min_diff
}
// </vc-code>


}

fn main() {}