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
/* helper modified by LLM (iteration 5): Fixed String length method from unicode_len() to len() */
fn parse_lines(input: &String) -> (lines: Vec<String>)
    ensures
        lines@.len() <= 2,
        forall|i: int| 0 <= i < lines@.len() ==> lines@[i]@ == parse_input(input@)[i],
{
    let mut lines = Vec::new();
    let mut current = String::from_str("");
    let mut i = 0;
    while i < input.len()
        invariant
            0 <= i <= input@.len(),
            lines@.len() <= 1,
            current@.len() <= input@.len(),
    {
        if input.get_char(i) == '\n' {
            lines.push(current);
            current = String::from_str("");
            if lines.len() >= 2 {
                break;
            }
        } else {
            current.push(input.get_char(i));
        }
        i = i + 1;
    }
    if current.len() > 0 && lines.len() < 2 {
        lines.push(current);
    }
    lines
}

fn parse_nat(s: &String) -> (n: usize)
    ensures
        n as int == string_to_int(s@),
{
    let mut result: usize = 0;
    let mut i: usize = 0;
    while i < s.len()
        invariant
            0 <= i <= s@.len(),
            result <= usize::MAX,
    {
        let c = s.get_char(i);
        if c >= '0' && c <= '9' {
            let digit = (c as usize) - ('0' as usize);
            result = result * 10 + digit;
        }
        i = i + 1;
    }
    result
}

fn transform_string(s: &String, key: usize) -> (result: String)
    requires
        s@.len() > 0,
        is_all_digits(s@),
        key <= 10,
    ensures
        result@.len() == s@.len(),
        result@ == transform_digits(s@, key as int),
{
    let mut result = String::from_str("");
    let mut i: usize = 0;
    while i < s.len()
        invariant
            0 <= i <= s@.len(),
            result@.len() == i,
            result@ == transform_digits(s@.take(i as int), key as int),
    {
        let c = s.get_char(i);
        let digit_val = (c as usize) - ('0' as usize);
        let new_digit = (digit_val + key) % 10;
        let new_char = (('0' as u8) + (new_digit as u8)) as char;
        result.push(new_char);
        i = i + 1;
    }
    result
}

fn rotate_str(s: &String, index: usize) -> (result: String)
    requires
        index < s@.len(),
    ensures
        result@ == rotate_string(s@, index as int),
{
    let mut result = String::from_str("");
    let mut i = index;
    while i < s.len()
        invariant
            index <= i <= s@.len(),
            result@ == s@.subrange(index as int, i as int),
    {
        result.push(s.get_char(i));
        i = i + 1;
    }
    let mut j = 0;
    while j < index
        invariant
            0 <= j <= index,
            result@ == s@.skip(index as int).add(s@.take(j as int)),
    {
        result.push(s.get_char(j));
        j = j + 1;
    }
    result
}

fn modify_at_index(s: &String, index: usize) -> (result: String)
    requires
        index < s@.len(),
        is_all_digits(s@),
    ensures
        result@ == modify_string(s@, index as int),
{
    let c = s.get_char(index);
    let key = if c == '0' { 0 } else { 10 - ((c as usize) - ('0' as usize)) };
    let transformed = transform_string(s, key);
    rotate_str(&transformed, index)
}

fn compare_digit_strings(a: &String, b: &String) -> (less: bool)
    requires
        is_all_digits(a@),
        is_all_digits(b@),
        a@.len() == b@.len(),
    ensures
        less == (string_to_int(a@) <= string_to_int(b@)),
{
    if a.len() == 0 {
        return true;
    }
    let mut i: usize = 0;
    while i < a.len()
        invariant
            0 <= i <= a@.len(),
    {
        let ca = a.get_char(i);
        let cb = b.get_char(i);
        if ca < cb {
            return true;
        } else if ca > cb {
            return false;
        }
        i = i + 1;
    }
    true
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
    /* code modified by LLM (iteration 5): Fixed String length method from unicode_len() to len() */
    let lines = parse_lines(&stdin_input);
    if lines.len() < 2 {
        return String::from_str("\n");
    }
    
    let n = parse_nat(&lines[0]);
    let digits = &lines[1];
    
    if n == 0 || digits.len() != n {
        return String::from_str("\n");
    }
    
    let mut valid = true;
    let mut i: usize = 0;
    while i < n
        invariant
            0 <= i <= n,
            valid == (forall|j: int| 0 <= j < i ==> digits@[j] >= '0' && digits@[j] <= '9'),
    {
        let c = digits.get_char(i);
        if c < '0' || c > '9' {
            valid = false;
            break;
        }
        i = i + 1;
    }
    
    if !valid {
        return String::from_str("\n");
    }
    
    let mut min_result = modify_at_index(digits, 0);
    let mut idx: usize = 1;
    
    while idx < n
        invariant
            1 <= idx <= n,
            min_result@.len() == n as int,
            is_all_digits(min_result@),
            exists|j: int| 0 <= j < idx && min_result@ == modify_string(digits@, j),
            forall|j: int| 0 <= j < idx ==> string_to_int(min_result@) <= string_to_int(modify_string(digits@, j)),
    {
        let candidate = modify_at_index(digits, idx);
        if compare_digit_strings(&candidate, &min_result) {
            min_result = candidate;
        }
        idx = idx + 1;
    }
    
    min_result.push('\n');
    min_result
}
// </vc-code>


}

fn main() {}