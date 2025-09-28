// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn can_form_non_ascending_sequence(rectangles: Seq<(int, int)>) -> bool {
    if rectangles.len() <= 1 {
        true
    } else {
        can_form_non_ascending_sequence_helper(rectangles, 1, max_spec(rectangles[0].0, rectangles[0].1))
    }
}

spec fn can_form_non_ascending_sequence_helper(rectangles: Seq<(int, int)>, index: int, prev_height: int) -> bool
    recommends 0 <= index <= rectangles.len()
    decreases rectangles.len() - index
{
    if index >= rectangles.len() {
        true
    } else {
        let a = rectangles[index].0;
        let b = rectangles[index].1;
        let min_dim = min_spec(a, b);
        let max_dim = max_spec(a, b);

        if min_dim > prev_height {
            false
        } else if min_dim <= prev_height < max_dim {
            can_form_non_ascending_sequence_helper(rectangles, index + 1, min_dim)
        } else {
            can_form_non_ascending_sequence_helper(rectangles, index + 1, max_dim)
        }
    }
}

spec fn parse_rectangles(input: Seq<char>) -> Seq<(int, int)> {
    /* Placeholder for parsing logic */
    seq![]
}

spec fn min_spec(a: int, b: int) -> int {
    if a <= b { a } else { b }
}

spec fn max_spec(a: int, b: int) -> int {
    if a >= b { a } else { b }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): choose best height that does not exceed prev */
fn choose_height(prev: i64, a: i64, b: i64) -> Option<i64> {
    let max = if a >= b { a } else { b };
    let min = if a <= b { a } else { b };
    if max <= prev {
        Some(max)
    } else if min <= prev {
        Some(min)
    } else {
        None
    }
}

/* helper modified by LLM (iteration 3): parse all integers from input string using chars iteration */
fn parse_tokens(input: &str) -> Vec<i64> {
    let mut nums: Vec<i64> = Vec::new();
    let mut in_num: bool = false;
    let mut sign: i64 = 1;
    let mut num: i64 = 0;
    for c in input.chars() {
        if c == '-' {
            if in_num {
                nums.push(num * sign);
                num = 0;
            }
            in_num = true;
            sign = -1;
        } else if c >= '0' && c <= '9' {
            let d = (c as i64 - '0' as i64);
            num = num * 10 + d;
            in_num = true;
        } else {
            if in_num {
                nums.push(num * sign);
                num = 0;
                sign = 1;
                in_num = false;
            }
        }
    }
    if in_num {
        nums.push(num * sign);
    }
    nums
}

// </vc-helpers>

// <vc-spec>
fn solve(input: &str) -> (result: String)
    requires input@.len() > 0
    ensures result@ == "YES"@ || result@ == "NO"@
    /* ensures result@ == "YES"@ <==> can_form_non_ascending_sequence(parse_rectangles(input@)) */
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 3): parse input and check sequence */
{
    let tokens = parse_tokens(input);
    if tokens.len() == 0 {
        return (String::from("NO"));
    }
    let n = tokens[0] as usize;
    if tokens.len() < 1 + 2 * n {
        return (String::from("NO"));
    }
    let mut prev: i64 = {
        let a = tokens[1];
        let b = tokens[2];
        if a >= b { a } else { b }
    };
    let mut ok = true;
    let mut i: usize = 1;
    while i < n {
        let idx = 1 + 2 * i;
        let a = tokens[idx];
        let b = tokens[idx + 1];
        match choose_height(prev, a, b) {
            Some(h) => prev = h,
            None => { ok = false; break; }
        }
        i += 1;
    }
    let result = if ok { String::from("YES") } else { String::from("NO") };
    (result)
}

// </vc-code>


}

fn main() {}