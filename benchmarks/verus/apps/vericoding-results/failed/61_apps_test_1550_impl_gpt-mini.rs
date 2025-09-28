// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(n: int, digits: Seq<char>) -> bool {
    n > 0 && digits.len() == n && forall|i: int| 0 <= i < digits.len() ==> #[trigger] digits[i] >= '0' && #[trigger] digits[i] <= '9'
}

spec fn modify_string(s: Seq<char>, index: int) -> Seq<char> {
    let key = if s[index] == '0' { 0 } else { 10 - (s[index] as int - '0' as int) };
    let transformed = transform_digits(s, key);
    rotate_string(transformed, index)
}

spec fn transform_digits(s: Seq<char>, key: int) -> Seq<char>
    decreases s.len()
{
    if s.len() == 0 {
        seq![]
    } else {
        let digit = (s[0] as int - '0' as int + key) % 10;
        seq![('0' as int + digit) as char].add(transform_digits(s.skip(1), key))
    }
}

spec fn rotate_string(s: Seq<char>, index: int) -> Seq<char> {
    if s.len() == 0 {
        seq![]
    } else {
        s.skip(index).add(s.take(index))
    }
}

spec fn is_all_digits(s: Seq<char>) -> bool {
    forall|i: int| 0 <= i < s.len() ==> #[trigger] s[i] >= '0' && #[trigger] s[i] <= '9'
}

spec fn parse_input(input: Seq<char>) -> Seq<Seq<char>>
    decreases input.len()
{
    parse_input_helper(input, 0, seq![], seq![])
}

spec fn parse_input_helper(input: Seq<char>, i: int, current_line: Seq<char>, lines: Seq<Seq<char>>) -> Seq<Seq<char>>
    decreases input.len() - i
{
    if i >= input.len() {
        if current_line.len() > 0 { lines.push(current_line) } else { lines }
    } else if input[i] == '\n' {
        parse_input_helper(input, i + 1, seq![], lines.push(current_line))
    } else {
        parse_input_helper(input, i + 1, current_line.push(input[i]), lines)
    }
}

spec fn parse_int(s: Seq<char>) -> int
    decreases s.len()
{
    if s.len() == 0 {
        0
    } else if !('0' <= s[0] <= '9') {
        0
    } else {
        (s[0] as int - '0' as int) + 10 * parse_int(s.skip(1))
    }
}

spec fn string_to_int(s: Seq<char>) -> int
    decreases s.len()
{
    if s.len() == 0 {
        0
    } else if !('0' <= s[0] <= '9') {
        string_to_int(s.skip(1))
    } else {
        (s[0] as int - '0' as int) * pow(10, (s.len() - 1) as nat) + string_to_int(s.skip(1))
    }
}

spec fn pow(base: int, exp: nat) -> int
    decreases exp
{
    if exp == 0 {
        1
    } else {
        base * pow(base, (exp - 1) as nat)
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): transform_vec_bytes using u8 arithmetic without literal suffixes */
fn transform_vec_bytes(s: &Vec<u8>, key: u8) -> Vec<u8> {
    let mut res: Vec<u8> = Vec::new();
    let mut i: usize = 0;
    while i < s.len() {
        let digit = ((s[i] - b'0') + key) % (10 as u8);
        let byte = b'0' + digit;
        res.push(byte);
        i += 1;
    }
    res
}

/* helper modified by LLM (iteration 5): rotate_vec_bytes robust rotation */
fn rotate_vec_bytes(s: &Vec<u8>, index: usize) -> Vec<u8> {
    let n = s.len();
    if n == 0 { return Vec::new(); }
    let mut res: Vec<u8> = Vec::new();
    let idx = if index < n { index } else { 0 };
    if idx < n {
        res.extend_from_slice(&s[idx..]);
        if idx > 0 { res.extend_from_slice(&s[..idx]); }
    }
    res
}

/* helper modified by LLM (iteration 5): compute_candidate using computed u8 key */
fn compute_candidate(s: &Vec<u8>, index: usize) -> Vec<u8> {
    if s.len() == 0 || index >= s.len() { return Vec::new(); }
    let key: u8 = if s[index] == b'0' { 0 as u8 } else { (10 as u8) - (s[index] - b'0') };
    let transformed = transform_vec_bytes(s, key);
    rotate_vec_bytes(&transformed, index)
}

// </vc-helpers>

// <vc-spec>
fn solve(stdin_input: String) -> (result: String)
    requires
        stdin_input@.len() > 0,
        (exists|i: int| 0 <= i < stdin_input@.len() && stdin_input@[i] == '\n'),
    ensures
        result@.len() > 0,
        result@[result@.len() - 1] == '\n',
        ({
            let lines = parse_input(stdin_input@);
            if lines.len() >= 2 {
                let n = parse_int(lines[0]);
                let digits = lines[1];
                if valid_input(n, digits) {
                    let min_result = result@.take(result@.len() - 1);
                    min_result.len() == n &&
                    (forall|i: int| 0 <= i < min_result.len() ==> #[trigger] min_result[i] >= '0' && #[trigger] min_result[i] <= '9') &&
                    (exists|index: int| 0 <= index < n && min_result == modify_string(digits, index)) &&
                    (forall|index: int| 0 <= index < n ==> string_to_int(min_result) <= string_to_int(modify_string(digits, index)))
                } else {
                    result@ == seq!['\n']
                }
            } else {
                result@ == seq!['\n']
            }
        })
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): parse input and compute minimal transformed rotation */
    let bytes = stdin_input.as_bytes();
    let mut lines: Vec<Vec<u8>> = Vec::new();
    let mut cur: Vec<u8> = Vec::new();
    let mut i = 0usize;
    while i < bytes.len() {
        if bytes[i] == b'\n' {
            lines.push(cur);
            cur = Vec::new();
        } else {
            cur.push(bytes[i]);
        }
        i += 1;
    }
    if cur.len() > 0 {
        lines.push(cur);
    }

    if lines.len() < 2 {
        return String::from("\n");
    }

    // parse n
    let mut n_val: i32 = 0;
    let mut ok = true;
    let mut j = 0usize;
    while j < lines[0].len() {
        let c = lines[0][j];
        if c < b'0' || c > b'9' {
            ok = false;
            break;
        }
        n_val = n_val * 10 + ((c - b'0') as i32);
        j += 1;
    }
    if !ok || n_val <= 0 {
        return String::from("\n");
    }
    let n_usize = n_val as usize;

    let digits = &lines[1];
    if digits.len() != n_usize {
        return String::from("\n");
    }

    let mut k = 0usize;
    while k < digits.len() {
        let c = digits[k];
        if c < b'0' || c > b'9' {
            return String::from("\n");
        }
        k += 1;
    }

    // compute minimal candidate lexicographically
    let mut min_candidate = compute_candidate(digits, 0);
    let mut idx = 1usize;
    while idx < n_usize {
        let cand = compute_candidate(digits, idx);
        if cand < min_candidate {
            min_candidate = cand;
        }
        idx += 1;
    }

    // build result string and append newline
    let mut s = match String::from_utf8(min_candidate.clone()) {
        Ok(ss) => ss,
        Err(_) => String::new(),
    };
    s.push('\n');
    s
}

// </vc-code>


}

fn main() {}