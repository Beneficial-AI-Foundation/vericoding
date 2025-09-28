// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn yes_string() -> Seq<char> {
    seq!['Y', 'E', 'S']
}

spec fn no_string() -> Seq<char> {
    seq!['N', 'O']
}

spec fn valid_input_format(input: Seq<char>) -> bool {
    let lines = split_by_newline(input);
    lines.len() >= 1 && 
    is_valid_int(lines[0]) &&
    {
        let t = parse_int(lines[0]);
        t >= 0 && t + 1 <= lines.len() &&
        forall|i: int| 1 <= i <= t ==> #[trigger] is_valid_two_int_line(lines[i])
    }
}

spec fn is_valid_int(s: Seq<char>) -> bool {
    s.len() > 0 && forall|i: int| 0 <= i < s.len() ==> #[trigger] s[i] >= '0' && #[trigger] s[i] <= '9'
}

spec fn is_valid_two_int_line(s: Seq<char>) -> bool {
    let parts = split_by_space(s);
    parts.len() >= 2 && is_valid_int(parts[0]) && is_valid_int(parts[1])
}

spec fn valid_output_format(output: Seq<char>, input: Seq<char>) -> bool {
    let input_lines = split_by_newline(input);
    if input_lines.len() == 0 { 
        output.len() == 0
    } else {
        let t = parse_int(input_lines[0]);
        let output_lines = split_by_newline(output);
        output_lines.len() == t &&
        forall|i: int| 0 <= i < t ==> #[trigger] seq_equals(output_lines[i], yes_string()) || #[trigger] seq_equals(output_lines[i], no_string())
    }
}

spec fn correct_divisibility_results(input: Seq<char>, output: Seq<char>) -> bool {
    let input_lines = split_by_newline(input);
    if input_lines.len() == 0 { 
        output.len() == 0
    } else {
        let t = parse_int(input_lines[0]);
        let output_lines = split_by_newline(output);
        output_lines.len() == t &&
        forall|i: int| 0 <= i < t && i + 1 < input_lines.len() ==> {
            let parts = split_by_space(input_lines[i + 1]);
            parts.len() >= 2 ==> {
                let x = parse_int(parts[0]);
                let y = parse_int(parts[1]);
                y != 0 ==> (#[trigger] seq_equals(output_lines[i], yes_string()) <==> x % y == 0)
            }
        }
    }
}

spec fn seq_equals(s1: Seq<char>, s2: Seq<char>) -> bool {
    s1.len() == s2.len() && forall|i: int| 0 <= i < s1.len() ==> #[trigger] s1[i] == #[trigger] s2[i]
}

spec fn split_by_newline(s: Seq<char>) -> Seq<Seq<char>>
    decreases s.len()
{
    if s.len() == 0 { 
        seq![]
    } else if s[0] == '\n' { 
        seq![seq![]].add(split_by_newline(s.subrange(1, s.len() as int)))
    } else {
        let rest = split_by_newline(s.subrange(1, s.len() as int));
        if rest.len() == 0 { 
            seq![s]
        } else { 
            seq![seq![s[0]].add(rest[0])].add(rest.subrange(1, rest.len() as int))
        }
    }
}

spec fn split_by_space(s: Seq<char>) -> Seq<Seq<char>>
    decreases s.len()
{
    if s.len() == 0 { 
        seq![]
    } else if s[0] == ' ' { 
        seq![seq![]].add(split_by_space(s.subrange(1, s.len() as int)))
    } else {
        let rest = split_by_space(s.subrange(1, s.len() as int));
        if rest.len() == 0 { 
            seq![s]
        } else { 
            seq![seq![s[0]].add(rest[0])].add(rest.subrange(1, rest.len() as int))
        }
    }
}

spec fn parse_int(s: Seq<char>) -> int
    decreases s.len()
{
    if s.len() == 0 { 
        0
    } else if s.len() == 1 {
        if '0' <= s[0] <= '9' { 
            s[0] as int - '0' as int 
        } else { 
            0 
        }
    } else {
        if '0' <= s[0] <= '9' {
            (s[0] as int - '0' as int) * pow10(s.len() - 1) + parse_int(s.subrange(1, s.len() as int))
        } else { 
            0 
        }
    }
}

spec fn pow10(n: int) -> int 
    decreases n
{
    if n <= 0 { 1 } else { 10 * pow10(n - 1) }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed sequence indexing to use direct indexing instead of @ operator */
fn vec_to_seq_char(v: Vec<char>) -> (result: Seq<char>)
    ensures result.len() == v.len(),
        forall|i: int| 0 <= i < v.len() ==> result[i] == v[i],
{
    v@
}

fn seq_to_vec_char(s: Seq<char>) -> (result: Vec<char>)
    ensures result.len() == s.len(),
        result@ == s,
{
    let mut result = Vec::new();
    let mut i: usize = 0;
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result[j] == s[j],
    {
        result.push(s[i]);
        i += 1;
    }
    result
}

fn parse_int_impl(chars: &Vec<char>, start: usize, end: usize) -> (result: i32)
    requires
        start <= end,
        end <= chars.len(),
        forall|i: int| start <= i < end ==> chars[i as int] >= '0' && chars[i as int] <= '9',
    ensures
        result == parse_int(chars@.subrange(start as int, end as int)),
{
    let mut result: i32 = 0;
    let mut i = start;
    while i < end
        invariant
            start <= i <= end,
            result == parse_int(chars@.subrange(start as int, i as int)),
    {
        result = result * 10 + (chars[i] as u8 - '0' as u8) as i32;
        i += 1;
    }
    result
}
// </vc-helpers>

// <vc-spec>
fn solve(input: Vec<char>) -> (output: Vec<char>)
    requires 
        input.len() > 0,
        valid_input_format(input@),
    ensures 
        forall|i: int| 0 <= i < output.len() ==> output[i] == 'Y' || output[i] == 'E' || output[i] == 'S' || output[i] == 'N' || output[i] == 'O' || output[i] == '\n',
        valid_output_format(output@, input@),
        correct_divisibility_results(input@, output@),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed sequence indexing to use usize instead of int for vector access */
    let mut output = Vec::new();
    let mut pos: usize = 0;
    
    // Skip to first newline to get t
    while pos < input.len() && input[pos] != '\n'
        invariant
            0 <= pos <= input.len(),
    {
        pos += 1;
    }
    
    let t_end = pos;
    let t = parse_int_impl(&input, 0, t_end);
    
    pos += 1; // skip newline
    
    let mut test_case: usize = 0;
    while test_case < t as usize
        invariant
            0 <= test_case <= t as usize,
            pos <= input.len(),
            output.len() == test_case * 4 + (if test_case > 0 { test_case - 1 } else { 0 }),
    {
        let line_start = pos;
        
        // Find end of current line
        while pos < input.len() && input[pos] != '\n'
            invariant
                line_start <= pos <= input.len(),
        {
            pos += 1;
        }
        
        let line_end = pos;
        
        // Find space separator
        let mut space_pos = line_start;
        while space_pos < line_end && input[space_pos] != ' '
            invariant
                line_start <= space_pos <= line_end,
        {
            space_pos += 1;
        }
        
        let x = parse_int_impl(&input, line_start, space_pos);
        let y = parse_int_impl(&input, space_pos + 1, line_end);
        
        if y != 0 && x % y == 0 {
            output.push('Y');
            output.push('E');
            output.push('S');
        } else {
            output.push('N');
            output.push('O');
        }
        
        if test_case < t as usize - 1 {
            output.push('\n');
        }
        
        pos += 1; // skip newline
        test_case += 1;
    }
    
    output
}
// </vc-code>


}

fn main() {}