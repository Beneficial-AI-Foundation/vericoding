// <vc-preamble>
use vstd::prelude::*;
use vstd::string::*;

verus! {

spec fn valid_input(input: Seq<char>) -> bool {
    input.len() > 0
}

spec fn valid_grid(grid: Seq<Seq<char>>, n: int, m: int) -> bool {
    n >= 1 && m >= 1 && grid.len() == n &&
    forall|i: int| 0 <= i < grid.len() ==> grid[i].len() == m
}

spec fn count_face_squares(input: Seq<char>) -> int
    decreases input.len()
{
    if input.len() == 0 {
        0
    } else {
        /* Parse input and count valid face squares */
        0  /* Placeholder - actual implementation would parse lines and count squares */
    }
}

spec fn count_face_squares_as_string(input: Seq<char>) -> Seq<char> {
    /* Convert count to string representation */
    seq!['0', '\n']  /* Placeholder */
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fix complex expression by converting string to char vector for indexing */
fn parse_and_count(input: &str) -> (count: i64)
    requires input@.len() > 0
    ensures count >= 0
{
    let lines: Vec<&str> = input.lines().collect();
    let first_line = lines[0];
    let parts: Vec<&str> = first_line.split_whitespace().collect();
    let n = parts[0].parse::<usize>().unwrap();
    let m = parts[1].parse::<usize>().unwrap();
    let mut count = 0;
    let mut i = 1;
    while i <= n
        invariant 1 <= i <= n + 1
        decreases n - i
    {
        if i < lines.len() {
            let row = lines[i];
            let row_chars: Vec<char> = row.chars().collect();
            let mut j = 0;
            while j < m - 1
                invariant 0 <= j <= m - 1
                decreases m - 1 - j
            {
                if i < n && j + 1 < row_chars.len() {
                    let c1 = row_chars[j];
                    let c2 = row_chars[j+1];
                    if i + 1 < lines.len() {
                        let next_row = lines[i+1];
                        let next_row_chars: Vec<char> = next_row.chars().collect();
                        let c3 = next_row_chars[j];
                        let c4 = next_row_chars[j+1];
                        let mut dot_count = 0;
                        let mut x_count = 0;
                        if c1 == '.' { dot_count += 1; } else if c1 == 'X' { x_count += 1; }
                        if c2 == '.' { dot_count += 1; } else if c2 == 'X' { x_count += 1; }
                        if c3 == '.' { dot_count += 1; } else if c3 == 'X' { x_count += 1; }
                        if c4 == '.' { dot_count += 1; } else if c4 == 'X' { x_count += 1; }
                        if dot_count == 2 && x_count == 2 {
                            count += 1;
                        }
                    }
                }
                j += 1;
            }
        }
        i += 1;
    }
    count as i64
}
// </vc-helpers>

// <vc-spec>
fn solve(input: String) -> (result: String)
    requires 
        valid_input(input@),
    ensures 
        result@.len() > 0,
        result@ == count_face_squares_as_string(input@)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fix newline in format string */
    let count = parse_and_count(&input);
    format!("{}\n", count)
}
// </vc-code>


}

fn main() {}