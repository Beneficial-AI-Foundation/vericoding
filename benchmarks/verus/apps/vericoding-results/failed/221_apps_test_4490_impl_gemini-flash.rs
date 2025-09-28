// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_dna_base(c: char) -> bool {
    c == 'A' || c == 'T' || c == 'C' || c == 'G'
}

spec fn dna_complement(c: char) -> char
    recommends valid_dna_base(c)
{
    if c == 'A' { 'T' }
    else if c == 'T' { 'A' }
    else if c == 'C' { 'G' }
    else if c == 'G' { 'C' }
    else { 'A' } /* default case for spec completeness */
}

spec fn find_newline(input: Seq<char>) -> int {
    choose|i: int| 0 <= i < input.len() && input[i] == '\n'
}

spec fn valid_input(input: Seq<char>) -> bool {
    let input_line = if exists|i: int| 0 <= i < input.len() && input[i] == '\n' {
        input.subrange(0, find_newline(input))
    } else {
        input
    };
    input_line.len() == 1 && valid_dna_base(input_line[0])
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): Removed all helper functions since all logic is handled in solve. */
// </vc-helpers>

// <vc-spec>
fn solve(stdin_input: &str) -> (result: String)
    requires stdin_input@.len() > 0
    ensures ({
        let input_seq = stdin_input@;
        let input_line = if exists|i: int| 0 <= i < input_seq.len() && input_seq[i] == '\n' {
            input_seq.subrange(0, find_newline(input_seq))
        } else {
            input_seq
        };
        if valid_input(input_seq) {
            result@ == seq![dna_complement(input_line[0]), '\n']
        } else {
            result@ == Seq::<char>::empty()
        }
    })
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 4): Fixed compilation errors related to `\n` and `nat`/`int` usage in non-ghost contexts, and refined the logic for `String::from_utf8`. */
{
        let input_seq = stdin_input@;
        let mut input_line: Seq<char>;
        let newline_found_in_input = exists|i: int| 0 <= i < input_seq.len() && input_seq[i] == '\n';

        if newline_found_in_input {
            let newline_idx = find_newline(input_seq);
            input_line = input_seq.subrange(0, newline_idx);
        } else {
            input_line = input_seq;
        }

        if input_line.len() == 1 && valid_dna_base(input_line[0]) {
            let complement_char = dna_complement(input_line[0]);
            let mut result_vec: Vec<char> = Vec::new();
            result_vec.push(complement_char);
            result_vec.push('\n');
            String::from_utf8(result_vec.into_iter().map(|c| c as u8).collect()).unwrap()
        } else {
            String::new()
        }
    }
// </vc-code>


}

fn main() {}