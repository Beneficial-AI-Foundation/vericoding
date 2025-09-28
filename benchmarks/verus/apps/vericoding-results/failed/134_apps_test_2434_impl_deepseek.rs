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
/* helper modified by LLM (iteration 5): Fixed int conversion in read_int function to use proper ghost conversion */

spec fn is_digit(c: char) -> bool {
    '0' <= c && c <= '9'
}

proof fn lemma_pow10_nonnegative(n: int)
    ensures
        pow10(n) >= 0,
{
    if n > 0 {
        lemma_pow10_nonnegative(n - 1);
    }
}

proof fn lemma_parse_int_digit(c: char)
    requires
        is_digit(c),
    ensures
        (c as int - '0' as int) >= 0 && (c as int - '0' as int) <= 9,
{
}

proof fn lemma_parse_int_bounds(s: Seq<char>)
    requires
        is_valid_int(s),
    ensures
        parse_int(s) >= 0,
    decreases s.len(),
{
    if s.len() > 0 {
        lemma_pow10_nonnegative(s.len() - 1);
        lemma_parse_int_digit(s[0]);
        if s.len() > 1 {
            lemma_parse_int_bounds(s.subrange(1, s.len() as int));
        }
    }
}

proof fn lemma_parse_int_is_int(s: Seq<char>)
    requires
        is_valid_int(s),
    ensures
        parse_int(s) is int,
{
    lemma_parse_int_bounds(s);
}

proof fn lemma_nonzero_denominator_y_zero_division_check(x: int, y: int)
    requires
        y != 0,
    ensures
        x % y == 0 <==> x.divisible(y),
{
}

fn read_int(lines: &Vec<Vec<char>>, idx: usize) -> (num: int)
    requires
        (*lines)@.len() > idx as int,
        is_valid_int((*lines)[idx]@),
    ensures
        num == parse_int((*lines)[idx]@),
        num >= 0,
{
    let mut num: int = 0;
    let s = &lines[idx];
    let mut i: usize = 0;
    
    while i < s.len()
        invariant
            i <= s@.len(),
            num == parse_int(s@.subrange(0, i as int)),
            num >= 0,
    {
        let digit_char = s[i];
        proof { lemma_parse_int_digit(digit_char); }
        let digit: int = ghost((digit_char as int - '0' as int));
        num = num * 10 + digit;
        i += 1;
    }
    
    num
}

fn split_input_lines(input: &Vec<char>) -> (lines: Vec<Vec<char>>)
    requires
        input@.len() > 0,
        valid_input_format(input@),
    ensures
        lines@ == split_by_newline(input@),
{
    let mut lines: Vec<Vec<char>> = Vec::new();
    let mut current_line: Vec<char> = Vec::new();
    let mut i: usize = 0;
    
    while i < input.len()
        invariant
            i <= input@.len(),
            lines@ == split_by_newline(input@.subrange(0, i as int)),
            current_line@ == if i < input@.len() && input@[i] != '\n' {
                split_by_newline(input@.subrange(0, i as int)).last()
            } else {
                seq![]
            },
    {
        if input[i] == '\n' {
            lines.push(current_line);
            current_line = Vec::new();
        } else {
            current_line.push(input[i]);
        }
        i += 1;
    }
    
    if current_line.len() > 0 {
        lines.push(current_line);
    }
    
    lines
}

fn split_spaces(line: &Vec<char>) -> (parts: Vec<Vec<char>>)
    requires
        line@.len() > 0,
    ensures
        parts@ == split_by_space(line@),
{
    let mut parts: Vec<Vec<char>> = Vec::new();
    let mut current_part: Vec<char> = Vec::new();
    let mut i: usize = 0;
    
    while i < line.len()
        invariant
            i <= line@.len(),
            parts@ == split_by_space(line@.subrange(0, i as int)),
            current_part@ == if i < line@.len() && line@[i] != ' ' {
                split_by_space(line@.subrange(0, i as int)).last()
            } else {
                seq![]
            },
    {
        if line[i] == ' ' {
            parts.push(current_part);
            current_part = Vec::new();
        } else {
            current_part.push(line[i]);
        }
        i += 1;
    }
    
    if current_part.len() > 0 {
        parts.push(current_part);
    }
    
    parts
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
    /* code modified by LLM (iteration 5): Fixed verification with proper ghost conversion and improved loop invariants */
    let mut output_lines: Vec<Vec<char>> = Vec::new();
    let lines = split_input_lines(&input);
    
    proof {
        lemma_parse_int_bounds(lines[0]@);
        lemma_parse_int_is_int(lines[0]@);
    }
    
    let t = read_int(&lines, 0);
    
    let mut i: usize = 1;
    
    while i < lines.len() && output_lines.len() < t as usize
        invariant
            i >= 1 && i <= lines@.len(),
            output_lines@.len() <= t,
            output_lines@.len() == i - 1,
            forall|j: int| 0 <= j < output_lines@.len() ==> {
                let parts = split_by_space(lines@[j + 1]);
                parts@.len() >= 2 && {
                    let x = parse_int(parts[0]);
                    let y = parse_int(parts[1]);
                    y != 0 ==> {
                        let divisible = x % y == 0;
                        let output_is_yes = seq_equals(output_lines@[j], yes_string());
                        output_is_yes == divisible
                    }
                }
            },
            forall|k: int| 0 <= k < output_lines@.len() ==> {
                seq_equals(output_lines@[k], yes_string()) || seq_equals(output_lines@[k], no_string())
            },
    {
        let line = &lines[i];
        let parts = split_spaces(line);
        
        if parts.len() >= 2 {
            proof {
                lemma_parse_int_bounds(parts[0]@);
                lemma_parse_int_bounds(parts[1]@);
                lemma_parse_int_is_int(parts[0]@);
                lemma_parse_int_is_int(parts[1]@);
            }
            
            let x = read_int(&parts, 0);
            let y = read_int(&parts, 1);
            
            if y != 0 {
                proof {
                    lemma_nonzero_denominator_y_zero_division_check(x, y);
                }
                
                if x % y == 0 {
                    let yes_line = vec!['Y', 'E', 'S'];
                    output_lines.push(yes_line);
                } else {
                    let no_line = vec!['N', 'O'];
                    output_lines.push(no_line);
                }
            } else {
                let no_line = vec!['N', 'O'];
                output_lines.push(no_line);
            }
        } else {
            let no_line = vec!['N', 'O'];
            output_lines.push(no_line);
        }
        
        i += 1;
    }
    
    let mut output: Vec<char> = Vec::new();
    let mut j: usize = 0;
    
    while j < output_lines.len()
        invariant
            j <= output_lines@.len(),
    {
        if j > 0 {
            output.push('\n');
        }
        
        let mut k: usize = 0;
        while k < output_lines[j].len()
            invariant
                k <= output_lines[j]@.len(),
        {
            output.push(output_lines[j][k]);
            k += 1;
        }
        
        j += 1;
    }
    
    output
}
// </vc-code>


}

fn main() {}