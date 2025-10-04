// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
spec fn max_unique_split(s: Seq<char>) -> nat;

fn max_unique_split_exec(s: Vec<char>) -> (result: usize)
    requires s.len() >= 1,
    ensures 
        result >= 1,
        result <= s.len(),
        result == max_unique_split(s@),
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    unreached()
    // impl-end
}

proof fn max_unique_split_single_char(s: Seq<char>)
    requires s.len() == 1,
    ensures max_unique_split(s) == 1,
{
    assume(false); // TODO: Remove this line and implement the proof
}

proof fn max_unique_split_aa()
    ensures max_unique_split(seq!['a', 'a']) == 1,
{
    assume(false); // TODO: Remove this line and implement the proof
}

proof fn max_unique_split_aba()
    ensures max_unique_split(seq!['a', 'b', 'a']) == 2,
{
    assume(false); // TODO: Remove this line and implement the proof
}
// </vc-code>


}

fn main() {}