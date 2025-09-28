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
/* helper modified by LLM (iteration 4): [Made proof in lemma_count_char_push more explicit] */
#[verifier::spinoff_prover]
proof fn lemma_count_char_push(s: Seq<char>, x: char, c: char)
    ensures
        count_char(s.push(x), c) == count_char(s, c) + (if x == c { 1int } else { 0int }),
    decreases s.len()
{
    if s.len() > 0 {
        lemma_count_char_push(s.subrange(1, s.len() as int), x, c);
        assert(s.push(x).subrange(1, s.push(x).len() as int) == s.subrange(1, s.len() as int).push(x));
        assert(count_char(s.push(x).subrange(1, s.push(x).len() as int), c) == count_char(s.subrange(1, s.len() as int).push(x), c));
    }
}

/* helper modified by LLM (iteration 4): [Relies on lemma_count_char_push, no complex proof needed] */
proof fn lemma_calculate_sum_push(s: Seq<char>, x: char)
    requires
        x == '+' || x == '-',
    ensures
        calculate_sum(s.push(x)) == calculate_sum(s) + if x == '+' { 1int } else { -1int },
{
    lemma_count_char_push(s, x, '+');
    lemma_count_char_push(s, x, '-');
}
// </vc-helpers>

// <vc-spec>
fn solve(s: Vec<char>) -> (result: i8)
    requires valid_input(s@)
    ensures result as int == calculate_sum(s@)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): [Added invariant to prove sum bounds and prevent overflow] */
    let mut sum: i8 = 0;
    let mut i: usize = 0;
    while i < 4
        invariant
            0 <= i <= 4,
            valid_input(s@),
            sum as int == calculate_sum(s@.subrange(0, i as int)),
            -(i as int) <= sum as int <= i as int,
        decreases 4 - i
    {
        proof {
            let sub_seq = s@.subrange(0, i as int);
            let next_char = s@[i as int];
            lemma_calculate_sum_push(sub_seq, next_char);
            assert(s@.subrange(0, i as int + 1) == sub_seq.push(next_char));
        }

        if s[i] == '+' {
            sum = sum + 1;
        } else {
            sum = sum - 1;
        }
        i = i + 1;
    }
    sum
}
// </vc-code>


}

fn main() {}