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
/* helper modified by LLM (iteration 5): spec helper to extract the first line */
spec fn first_line(input_seq: Seq<char>) -> Seq<char> {
    if exists|i: int| 0 <= i < input_seq.len() && input_seq[i] == '\n' {
        input_seq.subrange(0, find_newline(input_seq))
    } else {
        input_seq
    }
}

/* helper modified by LLM (iteration 5): spec helper to compute the desired output sequence */
spec fn desired_output(input_seq: Seq<char>) -> Seq<char> {
    let input_line = first_line(input_seq);
    if input_line.len() == 1 && valid_dna_base(input_line[0]) {
        seq![dna_complement(input_line[0]), '\n']
    } else {
        Seq::<char>::empty()
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
{
    /* code modified by LLM (iteration 5): construct output using std::string::String::from_chars from the spec-computed sequence */
    let input_seq = stdin_input@;
    let out_spec = desired_output(input_seq);
    std::string::String::from_chars(out_spec)
}
// </vc-code>


}

fn main() {}