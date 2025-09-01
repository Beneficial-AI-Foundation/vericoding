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
proof fn count_uppercase_sum_drop_last(seq: Seq<char>)
    requires
        seq.len() > 0,
    ensures
        count_uppercase_sum(seq) == count_uppercase_sum(seq.drop_last()) + 
            (if is_upper_case(seq.last()) { seq.last() as int } else { 0 }),
{
    reveal_with_fuel(count_uppercase_sum, 2);
}

proof fn count_uppercase_sum_append(seq1: Seq<char>, seq2: Seq<char>)
    ensures
        count_uppercase_sum(seq1 + seq2) == count_uppercase_sum(seq1) + count_uppercase_sum(seq2),
{
    if seq2.len() == 0 {
        assert(seq1 + seq2 == seq1);
        assert(count_uppercase_sum(seq1 + seq2) == count_uppercase_sum(seq1));
        assert(count_uppercase_sum(seq1) + count_uppercase_sum(seq2) == count_uppercase_sum(seq1) + 0);
    } else {
        count_uppercase_sum_append(seq1, seq2.drop_last());

        let s = seq1 + seq2;
        assert(s.drop_last() == seq1 + seq2.drop_last());
        assert(s.last() == seq2.last());

        count_uppercase_sum_drop_last(s);

        assert(count_uppercase_sum(s) == count_uppercase_sum(s.drop_last()) + 
            (if is_upper_case(s.last()) { s.last() as int } else { 0 }));

        assert(count_uppercase_sum(s) == count_uppercase_sum(seq1 + seq2.drop_last()) + 
            (if is_upper_case(seq2.last()) { seq2.last() as int } else { 0 }));

        assert(count_uppercase_sum(seq1 + seq2.drop_last()) == count_uppercase_sum(seq1) + count_uppercase_sum(seq2.drop_last()));

        assert(count_uppercase_sum(s) == count_uppercase_sum(seq1) + count_uppercase_sum(seq2.drop_last()) + 
            (if is_upper_case(seq2.last()) { seq2.last() as int } else { 0 }));

        assert(count_uppercase_sum(seq2) == count_uppercase_sum(seq2.drop_last()) + 
            (if is_upper_case(seq2.last()) { seq2.last() as int } else { 0 }));

        assert(count_uppercase_sum(s) == count_uppercase_sum(seq1) + count_uppercase_sum(seq2));
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
    let mut sum: u128 = 0;
    let mut i: usize = 0;
    while i < text.len()
        invariant
            0 <= i <= text.len(),
            sum == count_uppercase_sum(text@.subrange(0, i as int)),
    {
        let c = text[i];
        if is_upper_case(c) {
            sum += (c as u128);
        }
        i += 1;
    }
    sum
}
// </vc-code>

} // verus!
fn main() {}