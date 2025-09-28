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
    /* code modified by LLM (iteration 5): Use byte access instead of chars().nth() */
    let input_bytes = input.as_bytes();
    let mut lines: Vec<&str> = Vec::new();
    let mut start = 0;
    let mut i = 0;
    
    while i < input_bytes.len() {
        if input_bytes[i] == b'\n' {
            lines.push(&input[start..i]);
            start = i + 1;
        }
        i += 1;
    }
    
    let t = lines[0].parse::<usize>().unwrap();
    let mut output = String::new();
    
    for case_idx in 0..t {
        let x = lines[1 + 2*case_idx];
        let y = lines[2 + 2*case_idx];
        
        // Reverse x
        let x_bytes = x.as_bytes();
        let mut rev_x = String::new();
        let mut j = x_bytes.len();
        while j > 0 {
            j -= 1;
            rev_x.push(x_bytes[j] as char);
        }
        
        // Reverse y
        let y_bytes = y.as_bytes();
        let mut rev_y = String::new();
        let mut j = y_bytes.len();
        while j > 0 {
            j -= 1;
            rev_y.push(y_bytes[j] as char);
        }
        
        // Find first '1' in rev_y
        let rev_y_bytes = rev_y.as_bytes();
        let mut start_pos = 0;
        let mut idx = 0;
        while idx < rev_y_bytes.len() {
            if rev_y_bytes[idx] == b'1' {
                start_pos = idx;
                break;
            }
            idx += 1;
        }
        
        // Find first '1' in rev_x from start_pos
        let rev_x_bytes = rev_x.as_bytes();
        let mut offset = 0;
        let mut idx = start_pos;
        while idx < rev_x_bytes.len() {
            if rev_x_bytes[idx] == b'1' {
                offset = idx - start_pos;
                break;
            }
            idx += 1;
        }
        
        output.push_str(&offset.to_string());
        if case_idx < t - 1 {
            output.push('\n');
        }
    }
    
    output
}
// </vc-code>


}

fn main() {}