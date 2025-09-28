// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_binary_string(s: Seq<char>) -> bool {
    forall|i: int| 0 <= i < s.len() ==> (#[trigger] s[i] == '0' || #[trigger] s[i] == '1')
}

spec fn is_valid_integer(s: Seq<char>) -> bool {
    s.len() > 0 && (s[0] != '0' || s.len() == 1) && forall|i: int| 0 <= i < s.len() ==> ('0' <= #[trigger] s[i] <= '9')
}

spec fn count_char(s: Seq<char>, c: char) -> int
    decreases s.len()
{
    if s.len() == 0 { 0int }
    else { (if s[0] == c { 1int } else { 0int }) + count_char(s.subrange(1, s.len() as int), c) }
}

spec fn abs_diff_count(s: Seq<char>) -> int
    recommends is_binary_string(s)
{
    let count0 = count_char(s, '0');
    let count1 = count_char(s, '1');
    if count1 >= count0 { count1 - count0 } else { count0 - count1 }
}

spec fn int_to_string(n: int) -> Seq<char>
    recommends n >= 0
    decreases n
{
    if n == 0 { seq!['0'] }
    else if n < 10 { seq![char_of_digit(n)] }
    else { int_to_string(n / 10).add(seq![char_of_digit(n % 10)]) }
}

spec fn char_of_digit(d: int) -> char
    recommends 0 <= d <= 9
{
    if d == 0int { '0' }
    else if d == 1int { '1' }
    else if d == 2int { '2' }
    else if d == 3int { '3' }
    else if d == 4int { '4' }
    else if d == 5int { '5' }
    else if d == 6int { '6' }
    else if d == 7int { '7' }
    else if d == 8int { '8' }
    else if d == 9int { '9' }
    else { '0' }
}

spec fn string_to_int(s: Seq<char>) -> int
    recommends is_valid_integer(s)
    decreases s.len()
{
    if s.len() == 0 { 0int }
    else if s.len() == 1 { (s[0] as int) - ('0' as int) }
    else { string_to_int(s.subrange(0, s.len() - 1)) * 10int + ((s[s.len() - 1] as int) - ('0' as int)) }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): fixed invariant block format and unreachable code */
fn find_newline(v: &Vec<char>) -> (pos: usize)
    requires v@.len() > 0 && exists|i: int| 0 <= i < v@.len() && v@[i] == '\n'
    ensures 0 <= pos < v@.len() && v@[pos] == '\n' && forall|i: int| 0 <= i < pos ==> v@[i] != '\n'
{
    let mut i: usize = 0;
    while i < v.len()
        invariant {
            0 <= i <= v@.len(),
            forall|j: int| 0 <= j < i ==> v@[j] != '\n',
        }
        decreases (v@.len() - i)
    {
        if v[i] == '\n' {
            return i;
        }
        i += 1;
    }
    proof {
        let p = choose|p: int| 0<=p<v@.len() && v@[p]=='\n';
        assert(p < i);
        assert(v@[p] != '\n');
        assert(false);
    }
    unreachable!()
}

/* helper modified by LLM (iteration 2): fixed invariant block format */
fn find_token_end(v: &Vec<char>, start: usize) -> (end: usize)
    requires 0 <= start <= v@.len()
    ensures start <= end <= v@.len() && 
           (end == v@.len() || v@[end] == '\n') &&
           forall|i: int| start <= i < end ==> v@[i] != '\n'
{
    if start == v.len() {
        return start;
    }
    let mut end: usize = start;
    while end < v.len() && v[end] != '\n'
        invariant {
            start <= end <= v@.len(),
            forall|i: int| start <= i < end ==> v@[i] != '\n',
        }
        decreases (v@.len() - end)
    {
        end += 1;
    }
    end
}

/* helper modified by LLM (iteration 2): fixed invariant block format */
fn count_chars_in_slice(v: &Vec<char>, start: usize, end: usize, c: char) -> (count: usize)
    requires 0 <= start <= end <= v@.len()
    ensures count >= 0 && count <= end - start
{
    let mut count: usize = 0;
    let mut i: usize = start;
    while i < end
        invariant {
            start <= i <= end,
            count >= 0 && count <= i - start,
        }
        decreases (end - i)
    {
        if v[i] == c {
            count += 1;
        }
        i += 1;
    }
    count
}

/* helper modified by LLM (iteration 2): fixed invariant block format */
fn int_to_string_vec(n: usize) -> (s: Vec<char>)
    ensures s@ == int_to_string(n as int)
{
    if n == 0 {
        return vec!['0'];
    }
    let mut digits: Vec<char> = Vec::new();
    let mut num: usize = n;
    while num > 0
        invariant {
            num >= 0,
            digits@.len() >= 0,
        }
        decreases num
    {
        let digit = (num % 10) as u8;
        digits.push((digit + b'0') as char);
        num /= 10;
    }
    digits.reverse();
    digits
}
// </vc-helpers>

// <vc-spec>
fn solve(stdin_input: Vec<char>) -> (result: Vec<char>)
    requires 
        stdin_input@.len() > 0,
        exists|i: int| 0 <= i < stdin_input@.len() && stdin_input@[i] == '\n',
        exists|newline_pos: int| {
            0 <= newline_pos < stdin_input@.len() && stdin_input@[newline_pos] == '\n' &&
            newline_pos + 1 < stdin_input@.len() &&
            exists|binary_end: int| {
                newline_pos + 1 <= binary_end <= stdin_input@.len() &&
                (binary_end == stdin_input@.len() || stdin_input@[binary_end] == '\n') &&
                is_valid_integer(stdin_input@.subrange(0, newline_pos)) &&
                is_binary_string(stdin_input@.subrange(newline_pos + 1, binary_end))
            }
        },
    ensures 
        result@.len() > 0,
        result@[result@.len() - 1] == '\n',
        exists|newline_pos: int| {
            0 <= newline_pos < stdin_input@.len() && stdin_input@[newline_pos] == '\n' &&
            newline_pos + 1 < stdin_input@.len() &&
            exists|binary_end: int| {
                newline_pos + 1 <= binary_end <= stdin_input@.len() &&
                (binary_end == stdin_input@.len() || stdin_input@[binary_end] == '\n') &&
                is_binary_string(stdin_input@.subrange(newline_pos + 1, binary_end)) &&
                result@ == int_to_string(abs_diff_count(stdin_input@.subrange(newline_pos + 1, binary_end))).add(seq!['\n'])
            }
        },
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): no changes, helpers fixed */
    let newline_pos = find_newline(&stdin_input);
    let start = newline_pos + 1;
    let end = if start < stdin_input.len() {
        find_token_end(&stdin_input, start)
    } else {
        start
    };
    let count0 = count_chars_in_slice(&stdin_input, start, end, '0');
    let count1 = count_chars_in_slice(&stdin_input, start, end, '1');
    let abs_diff = if count1 >= count0 { count1 - count0 } else { count0 - count1 };
    let mut result = int_to_string_vec(abs_diff);
    result.push('\n');
    result
}
// </vc-code>


}
fn main() {}