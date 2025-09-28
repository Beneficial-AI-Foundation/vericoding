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
fn find_newline_impl(input: &str) -> (result: Option<usize>)
    ensures
        match result {
            Some(i) => 0 <= i < input.len() && input@.index(i as int) == '\n',
            None => forall|i: int| 0 <= i < input.len() ==> input@.index(i) != '\n',
        },
{
    let mut i = 0;
    while i < input.len()
        invariant
            0 <= i <= input.len(),
            forall|j: int| 0 <= j < i ==> input@.index(j) != '\n',
        decreases input.len() - i
    {
        if input.chars().nth(i).unwrap() == '\n' {
            return Some(i);
        }
        i += 1;
    }
    None
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
    let input_seq = stdin_input@;
    let newline_pos = find_newline_impl(stdin_input);
    
    let input_line = match newline_pos {
        Some(pos) => {
            let line = &stdin_input[..pos];
            assert(line@ == input_seq.subrange(0, pos as int));
            line
        },
        None => {
            assert(forall|i: int| 0 <= i < input_seq.len() ==> input_seq.index(i) != '\n');
            stdin_input
        }
    };
    
    if input_line.len() == 1 && valid_input(input_seq) {
        let c = input_line.chars().next().unwrap();
        let complement = if c == 'A' {
            'T'
        } else if c == 'T' {
            'A'
        } else if c == 'C' {
            'G'
        } else if c == 'G' {
            'C'
        } else {
            'A'
        };
        format!("{}\n", complement)
    } else {
        String::new()
    }
}
// </vc-code>


}

fn main() {}