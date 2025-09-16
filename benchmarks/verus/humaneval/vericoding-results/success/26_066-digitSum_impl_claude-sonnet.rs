// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_upper_case(c: char) -> (ret:bool) {
    c >= 'A' && c <= 'Z'
}

spec fn count_uppercase_sum(seq: Seq<char>) -> (ret:int)
    decreases seq.len(),
{
    if seq.len() == 0 {
        0
    } else {
        count_uppercase_sum(seq.drop_last()) + if is_upper_case(seq.last()) {
            seq.last() as int
        } else {
            0 as int
        }
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): added exec mode helper for runtime uppercase check */
fn is_upper_case_exec(c: char) -> (ret: bool)
    ensures
        ret == is_upper_case(c),
{
    c >= 'A' && c <= 'Z'
}

/* helper modified by LLM (iteration 4): lemma to prove relationship between recursive spec and subrange operations */
proof fn count_uppercase_sum_subrange_lemma(seq: Seq<char>, i: int)
    requires
        0 <= i <= seq.len(),
    ensures
        count_uppercase_sum(seq.subrange(0, i)) ==
        if i == 0 {
            0
        } else {
            count_uppercase_sum(seq.subrange(0, i - 1)) + if is_upper_case(seq[i - 1]) {
                seq[i - 1] as int
            } else {
                0
            }
        },
{
    if i == 0 {
        assert(seq.subrange(0, 0) =~= Seq::empty());
    } else {
        let sub_i = seq.subrange(0, i);
        let sub_i_minus_1 = seq.subrange(0, i - 1);
        assert(sub_i =~= sub_i_minus_1.push(seq[i - 1]));
        assert(sub_i.drop_last() =~= sub_i_minus_1);
        assert(sub_i.last() == seq[i - 1]);
    }
}
// </vc-helpers>

// <vc-spec>
fn digit_sum(text: &[char]) -> (sum: u128)

    ensures
        count_uppercase_sum(text@) == sum,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): fixed invariant with proper lemma application */
    let mut sum: u128 = 0;
    let mut i = 0;
    while i < text.len()
        invariant
            0 <= i <= text.len(),
            sum == count_uppercase_sum(text@.subrange(0, i as int)),
            sum <= i * 255,
        decreases text.len() - i
    {
        let c = text[i];
        if is_upper_case_exec(c) {
            proof {
                assert(c as u128 <= 255);
                assert(sum + c as u128 <= sum + 255);
            }
            sum = sum + c as u128;
        }
        i = i + 1;
        proof {
            count_uppercase_sum_subrange_lemma(text@, i as int);
        }
    }
    proof {
        assert(text@.subrange(0, text.len() as int) =~= text@);
    }
    sum
}
// </vc-code>

}
fn main() {}