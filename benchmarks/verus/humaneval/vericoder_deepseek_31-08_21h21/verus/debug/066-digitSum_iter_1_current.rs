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
        count_uppercase_sum(seq) == count_uppercase_sum(seq.drop_last(n)) + count_uppercase_sum(seq.subrange(seq.len() - n, seq.len())),
    decreases n,
{
    if n > 0 {
        let m = n - 1;
        count_uppercase_sum_recursive(seq, m);
        assert(seq.drop_last(n) == seq.drop_last(m).drop_last(1));
        assert(seq.subrange(seq.len() - n, seq.len()) == seq.subrange(seq.len() - m, seq.len()).drop_last(1).push(seq@[seq.len() - n]));
        
        if is_upper_case(seq@[seq.len() - n]) {
            assert(seq.subrange(seq.len() - n, seq.len())@.last() == seq@[seq.len() - n]);
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
    let mut sum: u128 = 0;
    let mut i: usize = 0;
    while i < text.len()
        invariant
            i <= text.len(),
            sum == count_uppercase_sum(text@.subrange(0, i)),
        decreases text.len() - i,
    {
        let c = text[i];
        if c >= 'A' && c <= 'Z' {
            proof {
                count_uppercase_sum_recursive(text@.subrange(0, i + 1), 1);
            }
            sum = sum + (c as u128);
        } else {
            proof {
                count_uppercase_sum_recursive(text@.subrange(0, i + 1), 1);
            }
        }
        i = i + 1;
    }
    proof {
        count_uppercase_sum_recursive(text@, text.len());
        assert(text@.drop_last(text.len()) == Seq::empty());
        assert(text@.subrange(0, text.len()) == text@);
    }
    sum
}
// </vc-code>

} // verus!
fn main() {}