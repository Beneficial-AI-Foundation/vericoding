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
/* helper modified by LLM (iteration 5): relate valid_input to first character being a valid base */
fn valid_input_implies_first_char_valid(input: Seq<char>)
    requires
        valid_input(input),
    ensures
        input.len() >= 1,
        valid_dna_base(input[0]),
{
    proof {
        let input_line = if exists|i: int| 0 <= i < input.len() && input[i] == '\n' {
            input.subrange(0, find_newline(input))
        } else {
            input
        };
        assert(input_line.len() == 1 && valid_dna_base(input_line[0]));
        assert(input_line[0] == input[0]);
        assert(input.len() >= 1);
        assert(valid_dna_base(input[0]));
    }
}
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
/* code modified by LLM (iteration 5): handle single-character input with optional newline, build result using String::from */
{
    let mut chars = stdin_input.chars();
    match chars.next() {
        None => String::from(""),
        Some(c) => {
            let next = chars.next();
            if valid_dna_base(c) && (next.is_none() || next == Some('\n')) {
                let mut out = String::from("");
                out.push(dna_complement(c));
                out.push('\n');
                out
            } else {
                String::from("")
            }
        }
    }
}
// </vc-code>


}

fn main() {}