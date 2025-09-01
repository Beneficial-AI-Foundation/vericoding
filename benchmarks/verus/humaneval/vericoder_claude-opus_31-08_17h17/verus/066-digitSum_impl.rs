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
proof fn count_uppercase_sum_append(seq: Seq<char>, c: char)
    ensures count_uppercase_sum(seq.push(c)) == count_uppercase_sum(seq) + if is_upper_case(c) { c as int } else { 0 }
    decreases seq.len()
{
    reveal_with_fuel(count_uppercase_sum, 2);
    assert(seq.push(c).drop_last() == seq);
    assert(seq.push(c).last() == c);
}

proof fn count_uppercase_sum_empty()
    ensures count_uppercase_sum(Seq::<char>::empty()) == 0
{
    reveal_with_fuel(count_uppercase_sum, 1);
}

proof fn count_uppercase_sum_bounds(seq: Seq<char>)
    ensures count_uppercase_sum(seq) >= 0,
            count_uppercase_sum(seq) <= seq.len() * 90
    decreases seq.len()
{
    reveal_with_fuel(count_uppercase_sum, 1);
    if seq.len() == 0 {
        assert(count_uppercase_sum(seq) == 0);
    } else {
        count_uppercase_sum_bounds(seq.drop_last());
        if is_upper_case(seq.last()) {
            assert(seq.last() >= 'A' && seq.last() <= 'Z');
            assert(seq.last() as int >= 65 && seq.last() as int <= 90);
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
    
    proof {
        count_uppercase_sum_empty();
    }
    
    while i < text.len()
        invariant
            0 <= i <= text.len(),
            sum == count_uppercase_sum(text@.subrange(0, i as int)) as u128,
            count_uppercase_sum(text@.subrange(0, i as int)) >= 0,
            count_uppercase_sum(text@.subrange(0, i as int)) <= i * 90,
            sum <= i * 90,
        decreases text.len() - i,
    {
        let c = text[i];
        let old_sum = sum;
        
        proof {
            count_uppercase_sum_bounds(text@.subrange(0, i as int));
            assert(i < text.len());
            assert(i * 90 < u128::MAX);
            assert(sum <= i * 90);
            if is_upper_case(c) {
                assert(c as int <= 90);
                assert(sum + 90 <= (i + 1) * 90);
                assert((i + 1) * 90 < u128::MAX);
            }
        }
        
        if c >= 'A' && c <= 'Z' {
            sum = sum + (c as u128);
        }
        
        proof {
            assert(text@.subrange(0, i as int).push(c) == text@.subrange(0, (i + 1) as int));
            count_uppercase_sum_append(text@.subrange(0, i as int), c);
            if is_upper_case(c) {
                assert(sum == old_sum + c as u128);
                assert(sum == count_uppercase_sum(text@.subrange(0, i as int)) as u128 + c as u128);
            } else {
                assert(sum == old_sum);
                assert(sum == count_uppercase_sum(text@.subrange(0, i as int)) as u128 + 0);
            }
            assert(sum == count_uppercase_sum(text@.subrange(0, (i + 1) as int)) as u128);
            count_uppercase_sum_bounds(text@.subrange(0, (i + 1) as int));
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