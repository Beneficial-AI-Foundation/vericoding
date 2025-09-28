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
    /* code modified by LLM (iteration 5): Use String::new() instead of String::with_capacity() */
    let input = stdin_input@;
    
    // Find newline position if it exists
    let mut newline_pos: Option<usize> = None;
    let mut i: usize = 0;
    let input_len = stdin_input.unicode_len();
    
    while i < input_len
        invariant
            0 <= i <= input_len,
            newline_pos.is_none() ==> forall|j: int| 0 <= j < i ==> input[j] != '\n',
            newline_pos.is_some() ==> {
                let pos = newline_pos.unwrap();
                0 <= pos < i && input[pos as int] == '\n'
            },
    {
        let chars = stdin_input.chars();
        let mut j: usize = 0;
        let mut found = false;
        let mut current_char = 'a';
        for c in chars {
            if j == i {
                current_char = c;
                found = true;
                break;
            }
            j = j + 1;
        }
        if found && current_char == '\n' {
            newline_pos = Some(i);
            break;
        }
        i = i + 1;
    }
    
    // Extract the input line (up to newline or end)
    let line_end = if newline_pos.is_some() {
        newline_pos.unwrap()
    } else {
        input_len
    };
    
    // Check if input is valid (single character that is a valid DNA base)
    if line_end == 1 {
        let chars = stdin_input.chars();
        let mut first_char = 'a';
        let mut char_found = false;
        for c in chars {
            if !char_found {
                first_char = c;
                char_found = true;
            }
        }
        
        if first_char == 'A' || first_char == 'T' || first_char == 'C' || first_char == 'G' {
            // Compute complement
            let complement = if first_char == 'A' {
                'T'
            } else if first_char == 'T' {
                'A'
            } else if first_char == 'C' {
                'G'
            } else {
                'C'
            };
            
            let mut result = String::new();
            result.push(complement);
            result.push('\n');
            return result;
        }
    }
    
    // Invalid input case
    String::new()
}
// </vc-code>


}

fn main() {}