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
proof fn count_uppercase_sum_nonnegative(seq: Seq<char>)
    ensures
        count_uppercase_sum(seq) >= 0,
    decreases seq.len(),
{
    if seq.len() > 0 {
        count_uppercase_sum_nonnegative(seq.drop_last());
    }
}

proof fn count_uppercase_sum_recursive(seq: Seq<char>, n: nat)
    requires
        n <= seq.len(),
    ensures
        count_uppercase_sum(seq) == count_uppercase_sum(seq.drop_last(n)) + count_uppercase_sum(seq.subrange(seq.len() as int - n as int, seq.len() as int)),
    decreases n,
{
    if n > 0 {
        let m: nat = (n - 1) as nat;
        count_uppercase_sum_recursive(seq, m);
        assert(seq.drop_last(n) == seq.drop_last(m).drop_last());
        assert(seq.subrange(seq.len() as int - n as int, seq.len() as int) == seq.subrange(seq.len() as int - m as int, seq.len() as int).drop_last().push(seq.index(seq.len() as int - n as int)));
        
        if is_upper_case(seq.index(seq.len() as int - n as int)) {
            assert(seq.subrange(seq.len() as int - n as int, seq.len() as int).last() == seq.index(seq.len() as int - n as int));
        }
        assert(count_uppercase_sum(seq) == count_uppercase_sum(seq.drop_last(m)) + if is_upper_case(seq.last()) { seq.last() as int } else { 0 });
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
            i <= text.len(),
            sum == count_uppercase_sum(text@.subrange(0, i as int)),
        decreases text.len() - i,
    {
        let c = text[i];
        if c >= 'A' && c <= 'Z' {
            proof {
                let sub_seq = text@.subrange(0, i as int + 1);
                assert(sub_seq.last() == c);
                assert(count_uppercase_sum(sub_seq) == count_uppercase_sum(sub_seq.drop_last()) + if is_upper_case(c) { c as int } else { 0 });
            }
            sum = sum + (c as u128);
        }
        i = i + 1;
    }
    proof {
        assert(text@.subrange(0, text.len() as int) == text@);
    }
    sum
}
// </vc-code>

} // verus!
fn main() {}