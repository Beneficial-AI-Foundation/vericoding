// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(input: Seq<char>) -> bool {
    input.len() > 0
}

spec fn valid_test_case(x1: int, y1: int, x2: int, y2: int) -> bool {
    1 <= x1 <= x2 && 1 <= y1 <= y2
}

spec fn count_different_sums(x1: int, y1: int, x2: int, y2: int) -> int
    recommends valid_test_case(x1, y1, x2, y2)
{
    (x2 - x1) * (y2 - y1) + 1
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): added decreases clause to while loop */
fn split_by_spaces(input: &Vec<char>) -> (tokens: Vec<Vec<char>>)
    ensures tokens@.len() >= 0
{
    let mut tokens = Vec::new();
    let mut current_token = Vec::new();
    let mut i = 0;
    while i < input.len()
        invariant
            i <= input.len(),
        decreases input.len() - i
    {
        let c = input[i];
        if c == ' ' {
            if current_token.len() > 0 {
                tokens.push(current_token);
                current_token = Vec::new();
            }
        } else {
            current_token.push(c);
        }
        i += 1;
    }
    if current_token.len() > 0 {
        tokens.push(current_token);
    }
    tokens
}

/* helper modified by LLM (iteration 3): added overflow check in arithmetic */
fn parse_int(token: &Vec<char>) -> (result: Option<i64>)
{
    if token.len() == 0 {
        return None;
    }
    let mut is_negative = false;
    let mut i = 0;
    if token[0] == '-' {
        if token.len() == 1 {
            return None;
        }
        is_negative = true;
        i = 1;
    }
    let mut value: i64 = 0;
    while i < token.len()
        invariant
            i <= token.len(),
            value >= 0,
        decreases token.len() - i
    {
        let c = token[i];
        if c >= '0' && c <= '9' {
            let digit = (c as i64) - ('0' as i64);
            // Check for overflow
            if value > (i64::MAX - digit) / 10 {
                return None;
            }
            value = value * 10 + digit;
            i += 1;
        } else {
            return None;
        }
    }
    if is_negative {
        Some(-value)
    } else {
        Some(value)
    }
}

/* helper modified by LLM (iteration 4): added invariant and decreases clause to second while loop */
fn int_to_string(n: i64) -> (s: Vec<char>)
    requires n >= 0
    ensures s@.len() >= 0
{
    if n == 0 {
        return vec!['0'];
    }
    let mut digits = Vec::new();
    let mut n = n;
    while n > 0
        invariant
            n >= 0,
        decreases n
    {
        let digit = n % 10;
        digits.push(('0' as u8 + digit as u8) as char);
        n = n / 10;
    }
    let mut s = Vec::new();
    let mut i = digits.len();
    while i > 0
        invariant
            i <= digits.len(),
            i >= 0,
        decreases i
    {
        i -= 1;
        s.push(digits[i]);
    }
    s
}
// </vc-helpers>

// <vc-spec>
fn solve(input: Vec<char>) -> (output: Vec<char>)
    requires valid_input(input@)
    ensures output@.len() >= 0
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): added overflow checks for arithmetic operations */
    let tokens = split_by_spaces(&input);
    if tokens.len() != 4 {
        return vec!['I','n','v','a','l','i','d'];
    }

    let parsed0 = parse_int(&tokens[0]);
    let parsed1 = parse_int(&tokens[1]);
    let parsed2 = parse_int(&tokens[2]);
    let parsed3 = parse_int(&tokens[3]);

    if let (Some(x1), Some(y1), Some(x2), Some(y2)) = (parsed0, parsed1, parsed2, parsed3) {
        if 1 <= x1 && x1 <= x2 && 1 <= y1 && y1 <= y2 {
            let diff_x = x2 - x1;
            let diff_y = y2 - y1;
            let product = diff_x.checked_mul(diff_y);
            let product = match product {
                Some(p) => p,
                None => return vec!['I','n','v','a','l','i','d'],
            };
            let result = product.checked_add(1);
            let result = match result {
                Some(r) => r,
                None => return vec!['I','n','v','a','l','i','d'],
            };
            return int_to_string(result);
        }
    }
    return vec!['I','n','v','a','l','i','d'];
}
// </vc-code>


}

fn main() {}