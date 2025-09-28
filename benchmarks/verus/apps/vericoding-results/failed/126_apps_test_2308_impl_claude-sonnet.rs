// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(input: Seq<char>) -> bool {
    let lines = split_lines(input);
    lines.len() >= 1 && 
    is_valid_number(lines[0]) &&
    {
        let t = string_to_int(lines[0]);
        t >= 0 && lines.len() >= 2 * t + 1 &&
        forall|i: int| 1 <= i < 2 * t + 1 ==> #[trigger] lines.len() > i && is_binary_string(lines[i]) && contains_one(lines[i])
    }
}

spec fn valid_output(output: Seq<char>, input: Seq<char>) -> bool {
    let lines = split_lines(input);
    lines.len() >= 1 ==> {
        let t = string_to_int(lines[0]);
        let output_lines = if output.len() == 0 { Seq::empty() } else { split_lines(output) };
        output_lines.len() == t &&
        forall|i: int| 0 <= i < t ==> #[trigger] is_valid_number(output_lines[i])
    }
}

spec fn correct_computation(output: Seq<char>, input: Seq<char>) -> bool {
    let lines = split_lines(input);
    lines.len() >= 1 ==> {
        let t = string_to_int(lines[0]);
        let output_lines = if output.len() == 0 { Seq::empty() } else { split_lines(output) };
        output_lines.len() == t &&
        forall|i: int| 0 <= i < t && 1 + 2*i < lines.len() && 2 + 2*i < lines.len() ==> {
            let x = lines[1 + 2*i];
            let y = lines[2 + 2*i];
            let rev_x = reverse(x);
            let rev_y = reverse(y);
            let start = index_of(rev_y, '1');
            start >= 0 &&
            {
                let offset = index_of_from(rev_x, '1', start);
                #[trigger] string_to_int(output_lines[i]) == offset
            }
        }
    }
}

spec fn is_binary_string(s: Seq<char>) -> bool {
    s.len() > 0 && forall|i: int| 0 <= i < s.len() ==> #[trigger] s.index(i) == '0' || s.index(i) == '1'
}

spec fn contains_one(s: Seq<char>) -> bool {
    exists|i: int| 0 <= i < s.len() && #[trigger] s.index(i) == '1'
}

spec fn is_valid_number(s: Seq<char>) -> bool {
    s.len() > 0 && forall|i: int| 0 <= i < s.len() ==> #[trigger] s.index(i) >= '0' && s.index(i) <= '9'
}

/* Helper functions */
spec fn split_lines(input: Seq<char>) -> Seq<Seq<char>> {
    arbitrary()
}

spec fn string_to_int(s: Seq<char>) -> int {
    arbitrary()
}

spec fn reverse(s: Seq<char>) -> Seq<char> {
    arbitrary()
}

spec fn index_of(s: Seq<char>, c: char) -> int {
    arbitrary()
}

spec fn index_of_from(s: Seq<char>, c: char, start: int) -> int {
    arbitrary()
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): use vstd::string for String::new() compatibility */
fn parse_lines(input: &str) -> (lines: Vec<vstd::string::String>)
    ensures
        lines@.len() > 0,
{
    let mut lines = Vec::new();
    let mut current = vstd::string::String::new();
    for c in input.chars()
        invariant
            lines@.len() >= 0,
    {
        if c == '\n' {
            if current.len() > 0 {
                lines.push(current.clone());
                current = vstd::string::String::new();
            }
        } else {
            current.push(c);
        }
    }
    if current.len() > 0 {
        lines.push(current);
    }
    lines
}

fn find_one_position(s: &str) -> (pos: usize)
    requires
        s@.len() > 0,
        contains_one(s@),
    ensures
        pos < s@.len(),
        s@.index(pos as int) == '1',
{
    let chars: Vec<char> = s.chars().collect();
    let mut i = 0;
    while i < chars.len()
        invariant
            i <= chars@.len(),
            contains_one(s@),
    {
        if chars[i] == '1' {
            return i;
        }
        i += 1;
    }
    0
}

fn find_one_from_position(s: &str, start: usize) -> (pos: i32)
    requires
        start <= s@.len(),
    ensures
        pos >= -1,
        pos >= 0 ==> pos < s@.len() as i32,
{
    let chars: Vec<char> = s.chars().collect();
    let mut i = start;
    while i < chars.len()
        invariant
            i >= start,
            i <= chars@.len(),
    {
        if chars[i] == '1' {
            return i as i32;
        }
        i += 1;
    }
    -1
}

fn reverse_string(s: &str) -> (result: vstd::string::String)
    requires
        s@.len() > 0,
    ensures
        result@.len() == s@.len(),
{
    let mut result = vstd::string::String::new();
    let chars: Vec<char> = s.chars().collect();
    let mut i = 0;
    while i < chars.len()
        invariant
            i <= chars.len(),
            result@.len() == i,
    {
        let idx = chars.len() - 1 - i;
        result.push(chars[idx]);
        i += 1;
    }
    result
}
// </vc-helpers>

// <vc-spec>
fn solve(input: &str) -> (output: String)
    requires
        input@.len() > 0,
        input@.index(input@.len() as int - 1) == '\n',
        valid_input(input@),
    ensures
        valid_output(output@, input@),
        output@.len() > 0 ==> output@.index(output@.len() as int - 1) != '\n',
        correct_computation(output@, input@),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): use vstd string types for compatibility */
    let lines = parse_lines(input);
    let t_str = lines[0].as_str();
    let t = t_str.parse::<usize>().unwrap();
    
    let mut results = Vec::new();
    
    for i in 0..t
        invariant
            i <= t,
            results@.len() == i,
    {
        let x = lines[1 + 2 * i].as_str();
        let y = lines[2 + 2 * i].as_str();
        
        let rev_x = reverse_string(x);
        let rev_y = reverse_string(y);
        
        let start = find_one_position(rev_y.as_str());
        let offset = find_one_from_position(rev_x.as_str(), start);
        
        let result_str = vstd::string::String::from_rust_string(offset.to_string());
        results.push(result_str);
    }
    
    let mut output = vstd::string::String::new();
    for i in 0..results.len()
        invariant
            i <= results@.len(),
    {
        if i > 0 {
            output.push('\n');
        }
        output = output + results[i].clone();
    }
    output.into_rust_string()
}
// </vc-code>


}

fn main() {}