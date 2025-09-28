// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(r: int) -> bool {
    1 <= r <= 100
}

spec fn dodecagon_area(r: int) -> int {
    3 * r * r
}

spec fn int_to_string(n: int) -> Seq<char>
    decreases n
{
    if n == 0 {
        seq!['0']
    } else if n < 10 {
        seq![('0' as int + n) as char]
    } else {
        int_to_string(n / 10) + int_to_string(n % 10)
    }
}

spec fn string_to_int(s: Seq<char>) -> int
    decreases s.len()
{
    if s.len() == 1 {
        (s[0] as int) - ('0' as int)
    } else if s.len() > 1 {
        string_to_int(s.subrange(0, s.len() - 1)) * 10 + ((s[s.len() - 1] as int) - ('0' as int))
    } else {
        0
    }
}
// </vc-preamble>

// <vc-helpers>
fn exec_string_to_int(s: &str) -> (result: i32)
    ensures
        result as int == string_to_int(s@),
{
    let mut n: i32 = 0;
    for c in s.chars() {
        let digit = (c as i32) - ('0' as i32);
        n = n * 10 + digit;
    }
    n
}

/* helper modified by LLM (iteration 5): replaced constant array with direct char conversion */
fn exec_int_to_string(n: i32) -> (result: String)
    ensures
        result@ == int_to_string(n as int),
{
    if n == 0 {
        return "0".to_string();
    }
    let mut n = n;
    let mut s = String::new();
    while n != 0 {
        let digit = n % 10;
        s.push(('0' as u8 + digit as u8) as char);
        n = n / 10;
    }
    let s_rev: String = s.chars().rev().collect();
    s_rev
}
// </vc-helpers>

// <vc-spec>
fn solve(stdin_input: &str) -> (output: String)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): using fixed helper functions */
{
    let r = exec_string_to_int(stdin_input);
    if r < 1 || r > 100 {
        return "Invalid input".to_string();
    }
    let area = 3 * r * r;
    let result = exec_int_to_string(area);
    result
}
// </vc-code>


}

fn main() {}