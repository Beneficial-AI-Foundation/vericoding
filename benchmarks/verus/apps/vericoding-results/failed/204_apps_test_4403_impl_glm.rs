// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(s: Seq<char>) -> bool {
    s.len() == 4 && forall|i: int| 0 <= i < s.len() ==> s[i] == '+' || s[i] == '-'
}

spec fn count_char(s: Seq<char>, c: char) -> int
    decreases s.len()
{
    if s.len() == 0 {
        0nat as int
    } else {
        (if s[0] == c { 1nat as int } else { 0nat as int }) + count_char(s.subrange(1, s.len() as int), c)
    }
}

spec fn calculate_sum(s: Seq<char>) -> int {
    count_char(s, '+') - count_char(s, '-')
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed integer literal suffixes */
proof fn lemma_count_char_for_len4(s: Seq<char>, c: char)
    requires s.len() == 4
    ensures count_char(s, c) == 
        (if s[0]==c { 1int } else { 0int }) +
        (if s[1]==c { 1int } else { 0int }) +
        (if s[2]==c { 1int } else { 0int }) +
        (if s[3]==c { 1int } else { 0int })
{
    let seq1 = s.subrange(1, s.len() as int);
    let seq2 = seq1.subrange(1, seq1.len() as int);
    let seq3 = seq2.subrange(1, seq2.len() as int);
    let seq4 = seq3.subrange(1, seq3.len() as int);

    assert(count_char(s, c) == (if s[0]==c { 1int } else { 0int }) + count_char(seq1, c));
    assert(count_char(seq1, c) == (if seq1[0]==c { 1int } else { 0int }) + count_char(seq2, c));
    assert(count_char(seq2, c) == (if seq2[0]==c { 1int } else { 0int }) + count_char(seq3, c));
    assert(count_char(seq3, c) == (if seq3[0]==c { 1int } else { 0int }) + count_char(seq4, c));
    assert(count_char(seq4, c) == 0int);

    assert(seq1[0] == s[1]);
    assert(seq2[0] == s[2]);
    assert(seq3[0] == s[3]);

    assert(count_char(s, c) == 
        (if s[0]==c { 1int } else { 0int }) +
        (if s[1]==c { 1int } else { 0int }) +
        (if s[2]==c { 1int } else { 0int }) +
        (if s[3]==c { 1int } else { 0int }));
}
// </vc-helpers>

// <vc-spec>
fn solve(s: Vec<char>) -> (result: i8)
    requires valid_input(s@)
    ensures result as int == calculate_sum(s@)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): fixed integer literal suffixes */
{
    let c0 = if s[0] == '+' { 1int } else { 0int };
    let c1 = if s[1] == '+' { 1int } else { 0int };
    let c2 = if s[2] == '+' { 1int } else { 0int };
    let c3 = if s[3] == '+' { 1int } else { 0int };
    let plus_count = c0 + c1 + c2 + c3;

    proof {
        lemma_count_char_for_len4(s@, '+');
    }

    let result_val = 2int * plus_count - 4int;
    result_val as i8
}
// </vc-code>


}

fn main() {}