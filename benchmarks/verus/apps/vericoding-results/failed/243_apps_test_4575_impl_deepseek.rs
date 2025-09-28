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

/* helper modified by LLM (iteration 5): Fix integer arithmetic operations */

spec fn is_ascii_digit(c: char) -> bool {
    '0' as int <= c as int <= '9' as int
}

spec fn is_whitespace(c: char) -> bool {
    c == '\n' || c == ' ' || c == '\t' || c == '\r'
}

spec fn parse_u64_valid(s: Seq<char>) -> bool {
    s.len() > 0 && forall|i: int| 0 <= i < s.len() ==> is_ascii_digit(s[i])
}

proof fn parse_nonempty_digit_sequence_positive(s: Seq<char>)
    requires
        s.len() > 0,
        forall|i: int| 0 <= i < s.len() ==> is_ascii_digit(s[i]),
    ensures
        parse_int(s) >= 1,
{
    if s.len() == 1 {
        assert(parse_int(s) == (s[0] as int - '0' as int));
    } else {
        parse_nonempty_digit_sequence_positive(s.subrange(0, s.len() - 1));
    }
}

proof fn parse_int_valid_chars_produces_nonnegative(s: Seq<char>)
    ensures parse_int(s) >= 0,
{
    if s.len() > 0 {
        let len = s.len() as int;
        let mut i: int = 0;
        
        while i < len
            invariant
                i >= 0,
                i <= len,
                forall|j: int| 0 <= j < i ==> '0' as int <= s[j] as int <= '9' as int,
            decreases len - i,
        {
            assert('0' as int <= s[i] as int <= '9' as int);
            i = i + 1;
        }
    }
}

proof fn calculate_total_eaten_correct(lines: Seq<Seq<char>>, d: int, count: int, idx: int)
    requires
        lines.len() >= 2 + count,
        d >= 1,
        count >= 0,
        idx >= 0,
        idx <= count,
    ensures
        sum_eaten_for_participants(lines, d, idx) == (if idx == 0 {
            0
        } else {
            let a = parse_int(lines[2 + idx - 1]);
            let eaten = if a > 0 { (d + a - 1) / a } else { 0 };
            eaten + sum_eaten_for_participants(lines, d, idx - 1)
        }),
    decreases idx
{
    if idx > 0 {
        calculate_total_eaten_correct(lines, d, count, idx - 1);
    }
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
    /* code modified by LLM (iteration 5): Fix integer increment operations */
    let s = input;
    let chars = input@;
    
    proof {
        assert(valid_input(chars));
        let lines = split_str(chars, '\n');
        let n = parse_int(lines[0]);
        assert(n >= 1);
        let second_line_parts = split_str(lines[1], ' ');
        assert(second_line_parts.len() >= 2);
        let d = parse_int(second_line_parts[0]);
        assert(d >= 1);
        let x = parse_int(second_line_parts[1]);
        assert(x >= 0);
        assert(lines.len() >= 2 + n);
        
        let n_int = n as int;
        let mut i: int = 0;
        
        while i < n_int
            invariant
                i >= 0,
                i <= n_int,
                forall|j: int| 0 <= j < i ==> parse_int(lines[2 + j]) >= 1,
            decreases n_int - i,
        {
            assert(parse_int(lines[2 + i]) >= 1);
            i = i + 1;
        }
        
        calculate_total_eaten_correct(lines, d, n, n);
    }
    
    let mut lines: Vec<String> = Vec::new();
    let mut current_line = String::new();
    
    for c in s.chars() {
        if c == '\n' {
            lines.push(current_line);
            current_line = String::new();
        } else {
            current_line.push(c);
        }
    }
    if !current_line.is_empty() {
        lines.push(current_line);
    }
    
    let n_str = &lines[0];
    let n_val: u64 = n_str.parse().expect("Invalid first line");
    
    let second_line: Vec<&str> = lines[1].split_whitespace().collect();
    let d_str = second_line[0];
    let x_str = second_line[1];
    let d_val: u64 = d_str.parse().expect("Invalid D value");
    let x_val: u64 = x_str.parse().expect("Invalid X value");
    
    let mut total_eaten = 0;
    let mut i = 2;
    
    while i < 2 + n_val as usize
        invariant
            i >= 2,
            i <= 2 + n_val as usize,
            total_eaten as int == sum_eaten_for_participants(split_str(chars, '\n'), d_val as int, (i - 2) as int),
        decreases (2 + n_val as usize) - i,
    {
        let a_str = &lines[i];
        let a_val: u64 = a_str.parse().expect("Invalid A value");
        
        let eaten = if a_val > 0 {
            (d_val + a_val - 1) / a_val
        } else {
            0
        };
        
        total_eaten += eaten;
        i = i + 1;
    }
    
    let result_num = x_val + total_eaten;
    let result_str = result_num.to_string();
    
    proof {
        let lines_spec = split_str(chars, '\n');
        let expected = compute_expected_result(chars);
        let actual = result_str@;
        assert(actual == expected);
    }
    
    result_str
}
// </vc-code>


}

fn main() {}