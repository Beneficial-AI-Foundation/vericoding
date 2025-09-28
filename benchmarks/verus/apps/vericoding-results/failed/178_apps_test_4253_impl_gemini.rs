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
fn parse_int(s: &str) -> (r: u64)
    requires
        s.is_ascii(),
        s.len() > 0,
        forall|i: int| 0 <= i < s.len() ==> '0' <= s.vspec_to_seq()@[i] && s.vspec_to_seq()@[i] <= '9',
    ensures
        r as int == string_to_int(s.vspec_to_seq()),
{
    let mut r: u64 = 0;
    let mut i: usize = 0;
    let s_bytes = s.as_bytes();
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            s.is_ascii(),
            s.len() > 0,
            forall|j: int| 0 <= j < s.len() ==> '0' <= s.vspec_to_seq()@[j] && s.vspec_to_seq()@[j] <= '9',
            r as int == string_to_int(s.vspec_to_seq().subrange(0, i as int)),
        decreases s.len() - i
    {
        let d = s_bytes[i] - b'0';
        r = r * 10u64 + (d as u64);
        i = i + 1;
    }
    r
}

fn int_to_string_exec(n: u64) -> (s: String)
    ensures
        s.vspec_to_seq() == int_to_string(n as int),
    decreases n,
{
    if n == 0 {
        return String::from_rust_string(std::string::String::from("0"));
    }
    if n < 10 {
        let ch = (b'0' + (n as u8)) as char;
        let mut s = String::new();
        s.push_char(ch);
        return s;
    }

    let mut s = int_to_string_exec(n / 10);
    let rem = n % 10;
    let rem_ch = (b'0' + (rem as u8)) as char;

    s.push_char(rem_ch);
    s
}

fn dodecagon_area_exec(r: u64) -> (area: u64)
    requires
        valid_input(r as int),
    ensures
        area as int == dodecagon_area(r as int),
{
    3 * r * r
}
// </vc-helpers>

// <vc-spec>
fn solve(stdin_input: &str) -> (output: String)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): [fixed compile error by using str::trim method] */
    // Assume the input is well-formed, satisfying preconditions of helper functions.
    // vstd::string::trim requires the string to be ASCII.
    let trimmed_s = stdin_input.trim();
    let r = parse_int(trimmed_s);
    assert(valid_input(r as int));
    let area = dodecagon_area_exec(r);
    int_to_string_exec(area)
}
// </vc-code>


}

fn main() {}