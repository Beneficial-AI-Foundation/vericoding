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
/* helper modified by LLM (iteration 5): fixed nat to usize conversion issue */
fn check_valid_input(input: &str) -> (valid: bool)
    ensures valid == valid_input(input@)
{
    let input_chars = input@;
    let line_end = if let Some(pos) = input.find('\n') {
        pos
    } else {
        input.len()
    };
    
    if line_end != 1 {
        return false;
    }
    
    let first_char = input.chars().nth(0).unwrap_or('X');
    first_char == 'A' || first_char == 'T' || first_char == 'C' || first_char == 'G'
}

fn get_complement_char(c: char) -> (result: char)
    requires valid_dna_base(c)
    ensures result == dna_complement(c)
{
    match c {
        'A' => 'T',
        'T' => 'A',
        'C' => 'G',
        'G' => 'C',
        _ => 'A'
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
    /* code modified by LLM (iteration 5): fixed nat to usize cast issue */
    if !check_valid_input(stdin_input) {
        return String::new();
    }
    
    let first_char = stdin_input.chars().nth(0).unwrap();
    let complement = get_complement_char(first_char);
    
    let mut result = String::new();
    result.push(complement);
    result.push('\n');
    
    proof {
        let input_seq = stdin_input@;
        let input_line = input_seq.subrange(0, 1);
        assert(input_line[0] == first_char);
        assert(complement == dna_complement(first_char));
        assert(result@ == seq![complement, '\n']);
        assert(result@ == seq![dna_complement(input_line[0]), '\n']);
    }
    
    result
}
// </vc-code>


}

fn main() {}