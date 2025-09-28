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
/* helper modified by LLM (iteration 5): changed to use lines() instead of split */
fn exec_split_lines(s: &str) -> Vec<String> {
    s.lines().map(|line| line.to_string()).collect()
}

/* helper modified by LLM (iteration 4): changed to use Rust types and avoid int/nat in non-ghost code */
fn exec_string_to_int(s: &str) -> isize {
    s.parse::<isize>().unwrap_or(0)
}

/* helper modified by LLM (iteration 4): changed to use Rust types and avoid int/nat in non-ghost code */
fn exec_reverse(s: &str) -> String {
    s.chars().rev().collect()
}

/* helper modified by LLM (iteration 4): changed to use Rust types and avoid int/nat in non-ghost code */
fn exec_index_of(s: &str, c: char) -> isize {
    s.find(c).map(|i| i as isize).unwrap_or(-1)
}

/* helper modified by LLM (iteration 5): replaced slicing with Vec<char> conversion to avoid unsupported slicing in exec code */
fn exec_index_of_from(s: &str, c: char, start: isize) -> isize {
    if start < 0 || start as usize >= s.len() {
        -1
    } else {
        let chars: Vec<char> = s.chars().collect();
        let mut idx = start as usize;
        while idx < chars.len() {
            if chars[idx] == c {
                return idx as isize;
            }
            idx += 1;
        }
        -1
    }
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
/* code modified by LLM (iteration 5): using fixed helper functions */
{
    let lines = exec_split_lines(input);
    let t = exec_string_to_int(&lines[0]);
    let mut results = Vec::new();
    let mut i = 0;
    while i < t {
        let x = &lines[1 + 2 * i as usize];
        let y = &lines[2 + 2 * i as usize];
        let rev_x = exec_reverse(x);
        let rev_y = exec_reverse(y);
        let start = exec_index_of(&rev_y, '1');
        let offset = exec_index_of_from(&rev_x, '1', start);
        let result_str = offset.to_string();
        results.push(result_str);
        i = i + 1;
    }
    results.join("\n")
}
// </vc-code>


}

fn main() {}