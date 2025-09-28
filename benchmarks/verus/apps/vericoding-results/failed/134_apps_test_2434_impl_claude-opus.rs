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
/* helper modified by LLM (iteration 5): Added proof blocks for ghost type comparisons */
fn split_input_by_newline(input: &Vec<char>) -> (lines: Vec<Vec<char>>)
    ensures
        lines@.len() == split_by_newline(input@).len(),
        forall|i: int| 0 <= i < lines@.len() ==> lines@[i]@ == split_by_newline(input@)[i],
{
    let mut lines = Vec::new();
    let mut current_line = Vec::new();
    let mut i = 0;
    
    while i < input.len()
        invariant
            0 <= i <= input.len(),
            lines@.len() <= split_by_newline(input@.subrange(0, i as int)).len(),
            current_line@.len() <= i,
        decreases input.len() - i
    {
        if input[i] == '\n' {
            lines.push(current_line);
            current_line = Vec::new();
        } else {
            current_line.push(input[i]);
        }
        i += 1;
    }
    
    if current_line.len() > 0 || (input.len() > 0 && input[input.len() - 1] == '\n') {
        lines.push(current_line);
    }
    
    lines
}

fn split_line_by_space(line: &Vec<char>) -> (parts: Vec<Vec<char>>)
    ensures
        parts@.len() >= 1,
        parts@.len() <= line@.len() + 1,
{
    let mut parts = Vec::new();
    let mut current_part = Vec::new();
    let mut i = 0;
    
    while i < line.len()
        invariant
            0 <= i <= line.len(),
            parts@.len() <= i + 1,
        decreases line.len() - i
    {
        if line[i] == ' ' {
            if current_part.len() > 0 {
                parts.push(current_part);
                current_part = Vec::new();
            }
        } else {
            current_part.push(line[i]);
        }
        i += 1;
    }
    
    if current_part.len() > 0 {
        parts.push(current_part);
    }
    
    if parts.len() == 0 {
        parts.push(Vec::new());
    }
    
    parts
}

fn parse_int_from_vec(s: &Vec<char>) -> (result: i32)
    requires
        s@.len() > 0,
        is_valid_int(s@),
        s@.len() <= 9,
        parse_int(s@) <= i32::MAX as int,
    ensures
        result >= 0,
        result as int == parse_int(s@),
{
    let mut result: i32 = 0;
    let mut i = 0;
    
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            result >= 0,
            result <= i32::MAX / 10,
            is_valid_int(s@),
        decreases s.len() - i
    {
        let c = s[i];
        assert(c >= '0' && c <= '9');
        let digit = #[verifier::truncate] (c as i32 - '0' as i32);
        assert(digit >= 0 && digit <= 9);
        result = result * 10 + digit;
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
    /* code modified by LLM (iteration 5): Fixed ghost type usage with proof blocks */
    let lines = split_input_by_newline(&input);
    
    assert(lines@.len() >= 1);
    assert(is_valid_int(lines@[0]@));
    
    let t_line = &lines[0];
    assert(t_line@.len() > 0);
    assert(t_line@.len() <= 9);
    proof {
        assert(parse_int(t_line@) <= i32::MAX as int);
    }
    
    let t = parse_int_from_vec(t_line);
    let mut output = Vec::new();
    let mut i: i32 = 0;
    
    while i < t
        invariant
            0 <= i <= t,
            t >= 0,
            i as int + 1 <= lines@.len(),
            output@.len() >= i * 3,
            output@.len() <= i * 4,
            forall|j: int| 0 <= j < output@.len() ==> 
                output@[j] == 'Y' || output@[j] == 'E' || output@[j] == 'S' || 
                output@[j] == 'N' || output@[j] == 'O' || output@[j] == '\n',
        decreases t - i
    {
        if (i as usize + 1) < lines.len() {
            let line = &lines[i as usize + 1];
            let parts = split_line_by_space(line);
            
            if parts.len() >= 2 && parts[0].len() > 0 && parts[1].len() > 0 {
                let part0 = &parts[0];
                let part1 = &parts[1];
                assert(part0@.len() > 0);
                assert(part1@.len() > 0);
                
                let mut can_parse = false;
                proof {
                    if is_valid_int(part0@) && is_valid_int(part1@) && 
                       part0@.len() <= 9 && part1@.len() <= 9 &&
                       parse_int(part0@) <= i32::MAX as int && parse_int(part1@) <= i32::MAX as int {
                        can_parse = true;
                    }
                }
                
                if can_parse && is_valid_int(part0@) && is_valid_int(part1@) && 
                   part0@.len() <= 9 && part1@.len() <= 9 {
                    let x = parse_int_from_vec(part0);
                    let y = parse_int_from_vec(part1);
                    
                    if y != 0 && x % y == 0 {
                        output.push('Y');
                        output.push('E');
                        output.push('S');
                    } else {
                        output.push('N');
                        output.push('O');
                    }
                } else {
                    output.push('N');
                    output.push('O');
                }
            } else {
                output.push('N');
                output.push('O');
            }
            
            if i < t - 1 {
                output.push('\n');
            }
        }
        
        i += 1;
    }
    
    output
}
// </vc-code>


}

fn main() {}