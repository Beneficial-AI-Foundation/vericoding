use vstd::prelude::*;

verus! {

spec fn is_upper_case(c: char) -> (ret:bool) {
    c >= 'A' && c <= 'Z'
}
// pure-end
// pure-end

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
// pure-end

// <vc-helpers>
fn digit_sum_rec(text: &[char]) -> (sum: u128)
    ensures
        count_uppercase_sum(text@) == sum,
    decreases
        text.len(),
{
    if text.len() == 0 {
        0
    } else {
        let n = text.len();
        let last = text[n - 1];
        let rest = &text[..n - 1];
        let sum_rest = digit_sum_rec(rest);
        // Relate the recursive definition of count_uppercase_sum to the Rust slice
        if is_upper_case(last) {
            proof {
                // Unfold the spec definition for count_uppercase_sum on the full sequence
                assert(count_uppercase_sum(text@) ==
                    count_uppercase_sum(text@.drop_last()) +
                    if is_upper_case(text@.last()) { text@.last() as int } else { 0 as int });
                // show rest@ equals text@.drop_last()
                // rest is the slice text[..n-1], so its sequence corresponds to dropping the last element
                assert(rest@.len() == n - 1);
                assert(text@.drop_last().len() == n - 1);
                // element-wise equality for all valid indices
                assert(forall |i: nat| i < rest@.len() ==> rest@[i] == text@[i]);
                assert(forall |i: nat| i < text@.drop_last().len() ==> text@.drop_last()@[i] == text@[i]);
                // therefore sequences are equal
                assert(rest@ == text@.drop_last());
                // last element equality
                assert(text@.last() == text@[n - 1]);
                assert(text@.last() == last);
                // use recursive postcondition sum_rest == count_uppercase_sum(rest@)
                assert(count_uppercase_sum(rest@) == sum_rest);
                // combine equalities to reach the desired equality
                assert(count_uppercase_sum(text@) == sum_rest + (last as int));
            }
            sum_rest + (last as u128)
        } else {
            proof {
                assert(count_uppercase_sum(text@) ==
                    count_uppercase_sum(text@.drop_last()) +
                    if is_upper_case(text@.last()) { text@.last() as int } else { 0 as int });
                assert(rest@.len() == n - 1);
                assert(text@.drop_last().len() == n - 1);
                assert(forall |i: nat| i < rest@.len() ==> rest@[i] == text@[i]);
                assert(forall |i: nat| i < text@.drop_last().len() ==> text@.drop_last()@[i] == text@[i]);
                assert(rest@ == text@.drop_last());
                assert(text@.last() == text@[n - 1]);
                assert(text@.last() == last);
                assert(count_uppercase_sum(rest@) == sum_rest);
                // since last is not uppercase, the added term is 0
                assert(!is_upper_case(last));
                assert(count_uppercase_sum(text@) == sum_rest);
            }
            sum_rest
        }
    }
}
// </vc-helpers>

// <vc-spec>
fn digit_sum(text: &[char]) -> (sum: u128)
    // post-conditions-start
    ensures
        count_uppercase_sum(text@) == sum,
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    digit_sum_rec(text)
}
// </vc-code>

} // verus!
fn main() {}