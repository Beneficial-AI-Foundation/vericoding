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
/* helper modified by LLM (iteration 5): reimplemented parsing using explicit match in loops to avoid `while let` */
fn parse_first_i64(s: &str) -> Option<i64> {
    let mut iter = s.chars();
    let mut c_opt = iter.next();

    // Skip leading whitespace using loop + match (no `while let`)
    loop {
        match c_opt {
            Some(c) if c == ' ' || c == '\n' || c == '\t' || c == '\r' => {
                c_opt = iter.next();
            }
            _ => { break; }
        }
    }

    if c_opt.is_none() { return None; }

    let mut sign: i64 = 1;
    let mut val: i64 = 0;
    let mut any = false;

    match c_opt {
        Some('+') => { c_opt = iter.next(); }
        Some('-') => { sign = -1; c_opt = iter.next(); }
        Some(c) => {
            if c >= '0' && c <= '9' {
                any = true;
                val = ((c as u32) - ('0' as u32)) as i64;
                c_opt = iter.next();
            } else {
                return None;
            }
        }
        None => { return None; }
    }

    // Accumulate digits
    loop {
        match c_opt {
            Some(ch) if ch >= '0' && ch <= '9' => {
                any = true;
                let d = (ch as u32 - '0' as u32) as i64;
                match val.checked_mul(10).and_then(|v| v.checked_add(d)) {
                    Some(v2) => { val = v2; }
                    None => { return None; }
                }
                c_opt = iter.next();
            }
            _ => { break; }
        }
    }

    if !any { return None; }

    match val.checked_mul(sign) {
        Some(v) => Some(v),
        None => None,
    }
}

/* helper modified by LLM (iteration 5): compute area in i128 to avoid overflow */
fn compute_area_i128(r: i64) -> i128 {
    let rr = r as i128;
    3i128 * rr * rr
}
// </vc-helpers>

// <vc-spec>
fn solve(stdin_input: &str) -> (output: String)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): use safe parser and i128 area computation; avoid unsupported `while let` in helpers */
    let opt = parse_first_i64(stdin_input);
    match opt {
        Some(r) => {
            let area = compute_area_i128(r);
            let mut out = area.to_string();
            out.push('\n');
            out
        }
        None => {
            String::new()
        }
    }
}
// </vc-code>


}

fn main() {}