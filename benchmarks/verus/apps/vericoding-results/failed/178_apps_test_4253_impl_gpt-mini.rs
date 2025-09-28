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
/* helper modified by LLM (iteration 5): parse digits from input using chars() */
fn parse_positive_int(s: &str) -> i128 {
    let mut res: i128 = 0;
    let mut started: bool = false;
    for c in s.chars() {
        if c >= '0' && c <= '9' {
            started = true;
            res = res * 10 + ((c as i32 - '0' as i32) as i128);
        } else if started {
            break;
        }
    }
    res
}

/* helper modified by LLM (iteration 5): compute dodecagon area as 3*r*r */
fn compute_area(r: i128) -> i128 {
    3 * r * r
}
// </vc-helpers>

// <vc-spec>
fn solve(stdin_input: &str) -> (output: String)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): parse integer using helper and convert to string without using unsupported as_bytes */
    let r = parse_positive_int(stdin_input);
    let area = compute_area(r);

    let mut n: i128 = area;
    let mut out = String::new();

    if n == 0 {
        out.push('0');
    } else {
        let mut rev: Vec<char> = Vec::new();
        while n > 0
            invariant
                n >= 0,
            decreases n
        {
            let rem = (n % 10) as u8;
            let ch = (('0' as u8) + rem) as char;
            rev.push(ch);
            n = n / 10;
        }

        let mut idx: usize = rev.len();
        while idx > 0
            invariant
                idx <= rev.len(),
            decreases idx
        {
            idx -= 1;
            out.push(rev[idx]);
        }
    }

    out
}
// </vc-code>


}

fn main() {}