// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(input: Seq<char>) -> bool {
    input.len() > 0 && 
    (input[0] == '0' || input[0] == '1') && 
    (input.len() == 1 || (input.len() > 1 && input[1] == '\n'))
}

spec fn logical_not(digit: char) -> Seq<char>
    recommends digit == '0' || digit == '1'
{
    if digit == '0' { seq!['1', '\n'] } else { seq!['0', '\n'] }
}

spec fn correct_output(input: Seq<char>, output: Seq<char>) -> bool
    recommends valid_input(input)
{
    output == logical_not(input[0])
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): predicate to recognize binary digits */
spec fn is_bit(c: char) -> bool {
    c == '0' || c == '1'
}

/* helper modified by LLM (iteration 5): function to compute the complement of a bit */
spec fn complement(c: char) -> char
    recommends is_bit(c)
{
    if c == '0' { '1' } else { '0' }
}

/* helper modified by LLM (iteration 5): lemma relating logical_not with complement */
proof fn lemma_logical_not_matches(c: char)
    requires
        is_bit(c),
    ensures
        logical_not(c) == seq![complement(c), '\n'],
{
    if c == '0' {
        assert(complement(c) == '1');
        assert(logical_not(c) == seq!['1', '\n']);
        assert(seq![complement(c), '\n'] == seq!['1', '\n']);
    } else {
        assert(complement(c) == '0');
        assert(logical_not(c) == seq!['0', '\n']);
        assert(seq![complement(c), '\n'] == seq!['0', '\n']);
    }
}

/* helper modified by LLM (iteration 5): from valid_input, the first character is a bit */
proof fn lemma_valid_input_implies_bit(input: Seq<char>)
    requires
        valid_input(input),
    ensures
        is_bit(input[0]),
{
    assert(is_bit(input[0]));
}
// </vc-helpers>

// <vc-spec>
fn solve(input: String) -> (output: String)
    requires valid_input(input@)
    ensures correct_output(input@, output@)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): select first spec char via choose (correct syntax), build complemented output, and prove correctness */
    let c: char = choose|ch: char| ch == input@[0];
    let mut out = String::new();
    if c == '0' {
        out.push('1');
    } else {
        out.push('0');
    }
    out.push('\n');
    proof {
        assert(c == input@[0]);
        assert(valid_input(input@));
        if input@[0] == '0' {
            assert(c == '0');
            assert(out@ == seq!['1', '\n']);
            assert(logical_not(input@[0]) == seq!['1', '\n']);
        } else {
            assert(input@[0] == '1');
            assert(c == '1');
            assert(out@ == seq!['0', '\n']);
            assert(logical_not(input@[0]) == seq!['0', '\n']);
        }
        assert(out@ == logical_not(input@[0]));
        assert(correct_output(input@, out@));
    }
    out
}
// </vc-code>


}

fn main() {}