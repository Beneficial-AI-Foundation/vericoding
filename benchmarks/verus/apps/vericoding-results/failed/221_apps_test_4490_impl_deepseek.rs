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
/* helper modified by LLM (iteration 5): replaced while let with index-based loop for char collection */
fn collect_chars(s: &str) -> Vec<char> {
    let mut result = Vec::new();
    let len = s.len();
    let mut i: usize = 0;
    while i < len
        invariant
            result@ == s@.subrange(0, result@.len() as int),
            i == result@.len() as int
        decreases len - i as int
    {
        result.push(s.chars().nth(i).unwrap());
        i = i + 1;
    }
    result
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
/* code modified by LLM (iteration 5): fixed implementation using safe char collection */
{
    let input_chars = collect_chars(stdin_input);
    
    if input_chars.is_empty() {
        return String::new();
    }
    
    let first_char = input_chars[0];
    
    if first_char == '\n' {
        return String::new();
    }
    
    if !valid_dna_base(first_char) {
        return String::new();
    }
    
    let complement = match first_char {
        'A' => 'T',
        'T' => 'A',
        'C' => 'G',
        'G' => 'C',
        _ => panic!("Unexpected character"),
    };
    
    let mut result = String::new();
    result.push(complement);
    result.push('\n');
    result
}
// </vc-code>


}

fn main() {}