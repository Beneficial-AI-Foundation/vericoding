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
        count_uppercase_sum(text.view()) == sum,
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
                assert(count_uppercase_sum(text.view()) ==
                    count_uppercase_sum(text.view().drop_last()) +
                    if is_upper_case(text.view().last()) { text.view().last() as int } else { 0 as int });
                // show rest.view() equals text.view().drop_last()
                assert(rest.view().len() == (n as int) - 1);
                assert(text.view().drop_last().len() == (n as int) - 1);
                // element-wise equality for all valid indices (use int indices)
                assert(forall |i: int| 0 <= i && i < rest.view().len() ==> rest.view()@[i] == text.view()@[i]);
                assert(forall |i: int| 0 <= i && i < text.view().drop_last().len() ==> text.view().drop_last()@[i] == text.view()@[i]);
                // therefore sequences are equal
                assert(rest.view() == text.view().drop_last());
                // last element equality
                assert(text.view().last() == text.view()[((n as int) - 1)]);
                assert(text.view().last() == last);
                // use recursive postcondition sum_rest == count_uppercase_sum(rest.view())
                assert(count_uppercase_sum(rest.view()) == sum_rest);
                // combine equalities to reach the desired equality
                assert(count_uppercase_sum(text.view()) == sum_rest + (last as int));
            }
            sum_rest + (last as u128)
        } else {
            proof {
                assert(count_uppercase_sum(text.view()) ==
                    count_uppercase_sum(text.view().drop_last()) +
                    if is_upper_case(text.view().last()) { text.view().last() as int } else { 0 as int });
                assert(rest.view().len() == (n as int) - 1);
                assert(text.view().drop_last().len() == (n as int) - 1);
                assert(forall |i: int| 0 <= i && i < rest.view().len() ==> rest.view()@[i] == text.view()@[i]);
                assert(forall |i: int| 0 <= i && i < text.view().drop_last().len() ==> text.view().drop_last()@[i] == text.view()@[i]);
                assert(rest.view() == text.view().drop_last());
                assert(text.view().last() == text.view()[((n as int) - 1)]);
                assert(text.view().last() == last);
                assert(count_uppercase_sum(rest.view()) == sum_rest);
                // since last is not uppercase, the added term is 0
                assert(!is_upper_case(last));
                assert(count_uppercase_sum(text.view()) == sum_rest);
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