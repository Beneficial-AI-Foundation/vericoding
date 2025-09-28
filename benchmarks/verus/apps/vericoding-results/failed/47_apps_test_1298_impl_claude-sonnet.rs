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
/* helper modified by LLM (iteration 5): fixed parameter type from int to nat */
proof fn lemma_count_char_subrange_property(s: Seq<char>, start: int, end: int, c: char)
    requires 0 <= start <= end <= s.len()
    ensures count_char(s.subrange(start, end), c) >= 0
    decreases end - start
{
    if start == end {
    } else {
        lemma_count_char_subrange_property(s, start + 1, end, c);
    }
}

proof fn lemma_abs_diff_count_valid(s: Seq<char>)
    requires is_binary_string(s)
    ensures abs_diff_count(s) >= 0
{
    lemma_count_char_subrange_property(s, 0, s.len() as int, '0');
    lemma_count_char_subrange_property(s, 0, s.len() as int, '1');
}

proof fn lemma_int_to_string_valid(n: nat)
    ensures int_to_string(n as int).len() > 0
    decreases n
{
    if n == 0 {
    } else if n < 10 {
    } else {
        lemma_int_to_string_valid(n / 10);
    }
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
    /* code modified by LLM (iteration 5): fixed type compatibility for lemma call */
    let mut newline_pos = 0;
    
    while newline_pos < stdin_input.len() && stdin_input[newline_pos] != '\n'
        invariant
            0 <= newline_pos <= stdin_input.len(),
            forall|i: int| 0 <= i < newline_pos ==> stdin_input@[i] != '\n',
    {
        newline_pos += 1;
    }
    
    let mut binary_end = newline_pos + 1;
    
    while binary_end < stdin_input.len() && stdin_input[binary_end] != '\n'
        invariant
            newline_pos + 1 <= binary_end <= stdin_input.len(),
            forall|i: int| newline_pos + 1 <= i < binary_end ==> stdin_input@[i] != '\n',
    {
        binary_end += 1;
    }
    
    let ghost binary_str = stdin_input@.subrange(newline_pos as int + 1, binary_end as int);
    
    let mut count0 = 0;
    let mut count1 = 0;
    let mut i = newline_pos + 1;
    
    while i < binary_end
        invariant
            newline_pos + 1 <= i <= binary_end,
            count0 == count_char(stdin_input@.subrange(newline_pos as int + 1, i as int), '0'),
            count1 == count_char(stdin_input@.subrange(newline_pos as int + 1, i as int), '1'),
    {
        if stdin_input[i] == '0' {
            count0 += 1;
        } else {
            count1 += 1;
        }
        i += 1;
    }
    
    let abs_diff = if count1 >= count0 { count1 - count0 } else { count0 - count1 };
    
    proof {
        lemma_abs_diff_count_valid(binary_str);
        lemma_int_to_string_valid(abs_diff as nat);
    }
    
    let mut result = Vec::new();
    let mut temp_n = abs_diff;
    let mut digits = Vec::new();
    
    if temp_n == 0 {
        digits.push('0');
    } else {
        while temp_n > 0
            invariant temp_n >= 0
        {
            let digit = (temp_n % 10) as u8;
            digits.push(('0' as u8 + digit) as char);
            temp_n = temp_n / 10;
        }
    }
    
    let mut j = digits.len();
    while j > 0
        invariant j <= digits.len()
    {
        j -= 1;
        result.push(digits[j]);
    }
    
    result.push('\n');
    result
}
// </vc-code>


}
fn main() {}