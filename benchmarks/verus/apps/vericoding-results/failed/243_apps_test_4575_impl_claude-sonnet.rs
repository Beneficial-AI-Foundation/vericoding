// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(input: Seq<char>) -> bool {
    let lines = split_str(input, '\n');
    lines.len() >= 2 &&
    parse_int(lines[0]) >= 1 &&
    {
        let n = parse_int(lines[0]);
        let second_line_parts = split_str(lines[1], ' ');
        second_line_parts.len() >= 2 &&
        parse_int(second_line_parts[0]) >= 1 &&
        parse_int(second_line_parts[1]) >= 0 &&
        lines.len() >= 2 + n &&
        forall|i: int| 0 <= i < n ==> #[trigger] parse_int(lines[2 + i]) >= 1
    }
}

spec fn compute_expected_result(input: Seq<char>) -> Seq<char>
    recommends valid_input(input)
{
    let lines = split_str(input, '\n');
    let n = parse_int(lines[0]);
    let second_line_parts = split_str(lines[1], ' ');
    let d = parse_int(second_line_parts[0]);
    let x = parse_int(second_line_parts[1]);
    let total_eaten = sum_eaten_for_participants(lines, d, n);
    int_to_string(x + total_eaten)
}

spec fn sum_eaten_for_participants(lines: Seq<Seq<char>>, d: int, count: int) -> int 
    recommends lines.len() >= 2 + count && d >= 1 && count >= 0
    decreases count
    when count >= 0
{
    if count == 0 {
        0
    } else {
        let a = parse_int(lines[2 + count - 1]);
        let eaten = if a > 0 { (d + a - 1) / a } else { 0 };
        eaten + sum_eaten_for_participants(lines, d, count - 1)
    }
}

spec fn split_str(s: Seq<char>, delimiter: char) -> Seq<Seq<char>> {
    if s.len() == 0 {
        seq![]
    } else {
        split_helper(s, delimiter, 0, 0, seq![])
    }
}

spec fn split_helper(s: Seq<char>, delimiter: char, start: int, current: int, acc: Seq<Seq<char>>) -> Seq<Seq<char>>
    recommends 0 <= start <= current <= s.len()
    decreases s.len() - current
    when 0 <= current <= s.len()
{
    if current == s.len() {
        if start == current {
            acc
        } else {
            acc.push(s.subrange(start, current))
        }
    } else if s[current] == delimiter {
        split_helper(s, delimiter, current + 1, current + 1, acc.push(s.subrange(start, current)))
    } else {
        split_helper(s, delimiter, start, current + 1, acc)
    }
}

spec fn parse_int(s: Seq<char>) -> int {
    if s.len() == 0 {
        0
    } else {
        parse_int_helper(s, 0, 0)
    }
}

spec fn parse_int_helper(s: Seq<char>, index: int, acc: int) -> int
    recommends 0 <= index <= s.len()
    decreases s.len() - index
    when 0 <= index <= s.len()
{
    if index == s.len() {
        acc
    } else if '0' <= s[index] <= '9' {
        parse_int_helper(s, index + 1, acc * 10 + (s[index] as int - '0' as int))
    } else {
        acc
    }
}

spec fn int_to_string(n: int) -> Seq<char> {
    if n == 0 {
        seq!['0']
    } else if n < 0 {
        seq!['-'] + int_to_string_helper(-n)
    } else {
        int_to_string_helper(n)
    }
}

spec fn int_to_string_helper(n: int) -> Seq<char>
    recommends n > 0
    decreases n
    when n > 0
{
    if n < 10 {
        seq![(n + '0' as int) as char]
    } else {
        int_to_string_helper(n / 10) + seq![(n % 10 + '0' as int) as char]
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed parse_int_helper_exec to use proper u8 arithmetic for digit conversion */
fn lemma_sum_eaten_for_participants_nonneg(lines: Seq<Seq<char>>, d: int, count: int)
    requires
        lines.len() >= 2 + count,
        d >= 1,
        count >= 0,
        forall|i: int| 0 <= i < count ==> parse_int(lines@[2 + i]) >= 1,
    ensures
        sum_eaten_for_participants(lines, d, count) >= 0,
    decreases count
{
    if count == 0 {
        // Base case: sum is 0
    } else {
        let a = parse_int(lines@[2 + count - 1]);
        assert(a >= 1);
        let eaten = if a > 0 { (d + a - 1) / a } else { 0 };
        assert(eaten >= 0);
        lemma_sum_eaten_for_participants_nonneg(lines, d, count - 1);
        assert(sum_eaten_for_participants(lines, d, count - 1) >= 0);
    }
}

exec fn sum_eaten_for_participants_exec(lines: Seq<Seq<char>>, d: int, count: int) -> (result: int)
    requires
        lines.len() >= 2 + count,
        d >= 1,
        count >= 0,
    ensures
        result == sum_eaten_for_participants(lines, d, count),
    decreases count
{
    if count == 0 {
        0
    } else {
        let a = parse_int(lines@[2 + count - 1]);
        let eaten = if a > 0 { (d + a - 1) / a } else { 0 };
        eaten + sum_eaten_for_participants_exec(lines, d, count - 1)
    }
}

exec fn parse_int_exec(s: Seq<char>) -> (result: int)
    ensures
        result == parse_int(s),
{
    if s.len() == 0 {
        0
    } else {
        parse_int_helper_exec(s, 0, 0)
    }
}

exec fn parse_int_helper_exec(s: Seq<char>, index: int, acc: int) -> (result: int)
    requires
        0 <= index <= s.len(),
    ensures
        result == parse_int_helper(s, index, acc),
    decreases s.len() - index
{
    if index == s.len() {
        acc
    } else if '0' <= s@[index] <= '9' {
        let digit_value = (s@[index] as u8 - '0' as u8) as int;
        parse_int_helper_exec(s, index + 1, acc * 10 + digit_value)
    } else {
        acc
    }
}

exec fn split_str_exec(s: Seq<char>, delimiter: char) -> (result: Vec<Vec<char>>)
    ensures
        result@ == split_str(s, delimiter),
{
    if s.len() == 0 {
        Vec::new()
    } else {
        split_helper_exec(s, delimiter, 0, 0, Vec::new())
    }
}

exec fn split_helper_exec(s: Seq<char>, delimiter: char, start: int, current: int, mut acc: Vec<Vec<char>>) -> (result: Vec<Vec<char>>)
    requires
        0 <= start <= current <= s.len(),
    ensures
        result@ == split_helper(s, delimiter, start, current, acc@),
    decreases s.len() - current
{
    if current == s.len() {
        if start == current {
            acc
        } else {
            let mut subseq = Vec::new();
            let mut i = start;
            while i < current
                invariant
                    start <= i <= current,
                    subseq@.len() == i - start,
                    forall|j: int| 0 <= j < i - start ==> subseq@[j] == s@[start + j],
            {
                subseq.push(s@[i]);
                i += 1;
            }
            acc.push(subseq);
            acc
        }
    } else if s@[current] == delimiter {
        let mut subseq = Vec::new();
        let mut i = start;
        while i < current
            invariant
                start <= i <= current,
                subseq@.len() == i - start,
                forall|j: int| 0 <= j < i - start ==> subseq@[j] == s@[start + j],
        {
            subseq.push(s@[i]);
            i += 1;
        }
        acc.push(subseq);
        split_helper_exec(s, delimiter, current + 1, current + 1, acc)
    } else {
        split_helper_exec(s, delimiter, start, current + 1, acc)
    }
}

exec fn int_to_string_exec(n: int) -> (result: Vec<char>)
    ensures
        result@ == int_to_string(n),
{
    if n == 0 {
        let mut result = Vec::new();
        result.push('0');
        result
    } else if n < 0 {
        let mut result = Vec::new();
        result.push('-');
        let positive_part = int_to_string_helper_exec(-n);
        let mut i = 0;
        while i < positive_part.len()
            invariant
                0 <= i <= positive_part.len(),
                result@.len() == 1 + i,
                result@[0] == '-',
                forall|j: int| 0 <= j < i ==> result@[1 + j] == positive_part@[j],
        {
            result.push(positive_part@[i]);
            i += 1;
        }
        result
    } else {
        int_to_string_helper_exec(n)
    }
}

exec fn int_to_string_helper_exec(n: int) -> (result: Vec<char>)
    requires
        n > 0,
    ensures
        result@ == int_to_string_helper(n),
    decreases n
{
    if n < 10 {
        let mut result = Vec::new();
        result.push((n as u8 + '0' as u8) as char);
        result
    } else {
        let mut prefix = int_to_string_helper_exec(n / 10);
        prefix.push(((n % 10) as u8 + '0' as u8) as char);
        prefix
    }
}

fn str_to_seq(s: &str) -> (result: Vec<char>)
    ensures
        result@.len() == s@.len(),
        forall|i: int| 0 <= i < s@.len() ==> result@[i] == s@[i],
{
    let mut result = Vec::new();
    let mut i = 0;
    while i < s.len()
        invariant
            0 <= i <= s@.len(),
            result@.len() == i,
            forall|j: int| 0 <= j < i ==> result@[j] == s@[j],
    {
        result.push(s.as_bytes()[i] as char);
        i += 1;
    }
    result
}

fn seq_to_string(s: &Vec<char>) -> (result: String)
    ensures
        result@.len() == s@.len(),
        forall|i: int| 0 <= i < s@.len() ==> result@[i] == s@[i],
{
    let mut result = String::new();
    let mut i = 0;
    while i < s.len()
        invariant
            0 <= i <= s@.len(),
            result@.len() == i,
            forall|j: int| 0 <= j < i ==> result@[j] == s@[j],
    {
        result.push(s@[i]);
        i += 1;
    }
    result
}
// </vc-helpers>

// <vc-spec>
fn solve(input: &str) -> (result: String)
    requires
        input@.len() > 0,
        valid_input(input@),
    ensures
        result@.len() > 0,
        result@ == compute_expected_result(input@),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed digit conversion by storing in temporary variable before casting */
    let input_seq = str_to_seq(input);
    
    let lines = split_str_exec(input_seq@, '\n');
    let n = parse_int_exec(lines@[0]);
    let second_line_parts = split_str_exec(lines@[1], ' ');
    let d = parse_int_exec(second_line_parts@[0]);
    let x = parse_int_exec(second_line_parts@[1]);
    
    proof {
        lemma_sum_eaten_for_participants_nonneg(lines@, d, n);
    }
    
    let total_eaten = sum_eaten_for_participants_exec(lines@, d, n);
    let result_int = x + total_eaten;
    let result_seq_chars = int_to_string_exec(result_int);
    
    let result = seq_to_string(&result_seq_chars);
    result
}
// </vc-code>


}

fn main() {}