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
proof fn lemma_take_plus_one(s: Seq<char>, i: int)
    requires
        0 <= i < s.len(),
    ensures
        count_uppercase_sum(s.take(i + 1)) == count_uppercase_sum(s.take(i)) + if is_upper_case(s[i]) { s[i] as int } else { 0 },
    decreases s.len() - i,
{
    let s_take_i = s.take(i);
    let s_take_i_plus_1 = s.take(i + 1);
    assert(s_take_i_plus_1.drop_last() == s_take_i);
    assert(s_take_i_plus_1.last() == s[i]);
}
// </vc-helpers>

// <vc-spec>
fn digit_sum(text: &[char]) -> (sum: u128)

    ensures
        count_uppercase_sum(text@) == sum,
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 4): Fixed type error by using @ operator for sequence indexing */
{
    let mut sum: u128 = 0;
    let mut i: usize = 0;
    while i < text.len()
        invariant
            0 <= i <= text.len(),
            sum as int == count_uppercase_sum(text@.take(i as int)),
            sum as int <= i as int * 'Z' as int,
        decreases text.len() - i,
    {
        let old_sum = sum;
        if text[i] >= 'A' && text[i] <= 'Z' {
            sum = sum + text[i] as u128;
        }
        proof {
            lemma_take_plus_one(text@, i as int);
            if text@[i as int] >= 'A' && text@[i as int] <= 'Z' {
                assert(is_upper_case(text@[i as int]));
                assert(sum as int == old_sum as int + text@[i as int] as int);
            } else {
                assert(!is_upper_case(text@[i as int]));
                assert(sum as int == old_sum as int);
            }
            assert(sum as int == count_uppercase_sum(text@.take((i + 1) as int)));
        }
        i = i + 1;
    }
    assert(text@.take(text.len() as int) == text@);
    sum
}
// </vc-code>

}
fn main() {}