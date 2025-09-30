// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(input: Seq<char>) -> bool {
    input.len() >= 3 &&
    input[1] == ' ' &&
    (input[0] == 'H' || input[0] == 'D') &&
    (input[2] == 'H' || input[2] == 'D') &&
    (input.len() == 3 || (input.len() > 3 && input[3] == '\n'))
}

spec fn correct_output(input: Seq<char>) -> Seq<char> {
    if (input[0] == 'H' && input[2] == 'H') || (input[0] == 'D' && input[2] == 'D') {
        seq!['H', '\n']
    } else {
        seq!['D', '\n']
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): relate correct_output to equality of first and third chars */
fn lemma_correct_output_equiv(input: Seq<char>)
    requires
        valid_input(input),
    ensures
        correct_output(input) == if (input[0] == input[2]) { seq!['H','\n'] } else { seq!['D','\n'] },
{
    proof {
        assert(valid_input(input));
        assert(input[0] == 'H' || input[0] == 'D');
        assert(input[2] == 'H' || input[2] == 'D');
        if input[0] == input[2] {
            assert((input[0] == 'H' && input[2] == 'H') || (input[0] == 'D' && input[2] == 'D'));
            assert(correct_output(input) == seq!['H','\n']);
        } else {
            assert(!((input[0] == 'H' && input[2] == 'H') || (input[0] == 'D' && input[2] == 'D')));
            assert(correct_output(input) == seq!['D','\n']);
        }
    }
}

// </vc-helpers>

// <vc-spec>
fn solve(input: Vec<char>) -> (result: Vec<char>)
    requires valid_input(input@)
    ensures result@ == correct_output(input@)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): use runtime Vec indexing instead of spec indexing */
{
    let mut out: Vec<char> = Vec::new();
    if input[0] == input[2] {
        out.push('H');
    } else {
        out.push('D');
    }
    out.push('\n');
    out
}

// </vc-code>


}

fn main() {}