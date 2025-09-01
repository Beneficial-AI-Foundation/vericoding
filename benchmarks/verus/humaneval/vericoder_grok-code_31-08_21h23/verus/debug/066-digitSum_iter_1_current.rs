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
// </vc-helpers>
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
    let ghost seq = text@;
    let mut sum: u128 = 0;
    let mut i: usize = 0;
    while i < text.len()
        invariant
            i <= text.len(),
            sum as int == count_uppercase_sum(seq.take(i as int)),
    {
        let add = if is_upper_case(text[i as int]) {
            (text[i as int] as int)
        } else {
            0
        };
        proof {
            let new_count = count_uppercase_sum(seq.take(i as int + 1));
            assert(seq.take(i as int + 1) == seq.take(i as int).push(text[i as int]));
            assert(new_count == count_uppercase_sum(seq.take(i as int)) + add);
            assert(new_count == sum as int + add);
        }
        sum = sum + (add as u128);
        i = i + 1;
    }
    proof {
        assert(i >= text.len());
        assert(i as int == seq.len());
        assert(sum as int == count_uppercase_sum(seq.take(seq.len())));
        assert(sum as int == count_uppercase_sum(seq));
        assert(sum <= 170141183460469231731687303715884105727u128);
    }
    sum
}
// </vc-code>

} // verus!
fn main() {}