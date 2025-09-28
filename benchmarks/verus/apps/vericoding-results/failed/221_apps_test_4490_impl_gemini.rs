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
/* helper modified by LLM (iteration 2): retained from previous attempt as they seem correct */
fn exec_valid_dna_base(c: char) -> (res: bool)
    ensures
        res == valid_dna_base(c),
{
    c == 'A' || c == 'T' || c == 'C' || c == 'G'
}

/* helper modified by LLM (iteration 2): retained from previous attempt as they seem correct */
fn exec_dna_complement(c: char) -> (res: char)
    requires
        valid_dna_base(c),
    ensures
        res == dna_complement(c),
{
    if c == 'A' {
        'T'
    } else if c == 'T' {
        'A'
    } else if c == 'C' {
        'G'
    } else {
        'C'
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
    /* code modified by LLM (iteration 2): Re-implemented using `vstd` byte/string ops to avoid unsupported `collect`. */
    let bytes = stdin_input.as_bytes();

    let mut line_len_bytes: usize = 0;
    while line_len_bytes < bytes.len() && bytes[line_len_bytes] != b'\n'
        invariant
            0 <= line_len_bytes <= bytes.len(),
            forall|i: int| 0 <= i < line_len_bytes ==> bytes@[i] != b'\n',
        decreases bytes.len() - line_len_bytes
    {
        line_len_bytes += 1;
    }

    let line_bytes_slice = &bytes[..line_len_bytes];
    let line_bytes_vec = Vec::from_slice(line_bytes_slice);
    let line_string = vstd::string::bytes_to_string(line_bytes_vec);

    if line_string.view().len() == 1 {
        let c = line_string.view()[0];
        if exec_valid_dna_base(c) {
            let complement = exec_dna_complement(c);
            let mut s = String::new();
            s.push(complement);
            s.push('\n');
            s
        } else {
            String::new()
        }
    } else {
        String::new()
    }
}
// </vc-code>


}

fn main() {}