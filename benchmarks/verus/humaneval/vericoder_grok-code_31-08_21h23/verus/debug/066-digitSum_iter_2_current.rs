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

fn is_upper_case_exec(c: char) -> (res: bool) {
    c >= 'A' && c <= 'Z'
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
    let ghost seq = text@;
    let mut sum: u128 = 0;
    let mut i: usize = 0;
    while i < text.len()
        invariant
            i <= text.len(),
            sum as int == count_uppercase_sum(seq.take(i as int)),
    {
        let add: u128 = if is_upper_case_exec(text[i]) {
            (text[i] as u32) as u128
        } else {
            0
        };
        proof {
            assert(is_upper_case_exec(seq@[i as int]) == is_upper_case(seq@[i as int]));
            let add_ghost: int = if is_upper_case(seq@[i as int]) {
                seq@[i as int] as int
            } else {
                0
            };
            assert(add as int == add_ghost);
            let new_count = count_uppercase_sum(seq.take(i as int + 1));
            assert(seq.take(i as int + 1) == seq.take(i as int).push(seq@[i as int]));
            assert(new_count == count_uppercase_sum(seq.take(i as int)) + add_ghost);
            assert(new_count == sum as int + add_ghost);
        }
        sum = sum + add;
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