use vstd::prelude::*;


verus! {

spec fn sum_negative_to(seq: Seq<i64>) -> (res: int)
    decreases seq.len(),
{
    if seq.len() == 0 {
        0
    } else {
        sum_negative_to(seq.drop_last()) + if (seq.last() < 0) {
            seq.last() as int
        } else {
            0 as int
        }
    }
}
// pure-end

// <vc-helpers>
proof fn sum_negative_to_empty(seq: Seq<i64>)
    requires seq.len() == 0
    ensures sum_negative_to(seq) == 0
{
}

proof fn sum_negative_to_extend(seq: Seq<i64>, elem: i64)
    requires seq.len() > 0,
        seq.last() == elem
    ensures sum_negative_to(seq) == sum_negative_to(seq.drop_last()) + if elem < 0 { elem as int } else { 0 }
{
}

proof fn sum_negative_to_prefix(seq: Seq<i64>, i: int)
    requires 0 <= i <= seq.len()
    ensures sum_negative_to(seq.subrange(0, i)) == sum_negative_to(seq.subrange(0, i))
    decreases i
{
}

proof fn sum_negative_to_increment(seq: Seq<i64>, i: int)
    requires 0 <= i < seq.len()
    ensures sum_negative_to(seq.subrange(0, i + 1)) == 
            sum_negative_to(seq.subrange(0, i)) + if seq[i] < 0 { seq[i] as int } else { 0 }
{
    let prefix = seq.subrange(0, i);
    let extended = seq.subrange(0, i + 1);
    assert(extended == prefix.push(seq[i]));
    assert(extended.drop_last() == prefix);
    assert(extended.last() == seq[i]);
}

proof fn sum_bounds_preserved(old_sum: i128, new_elem: i64)
    requires 
        old_sum >= i128::MIN / 2,
        old_sum <= i128::MAX / 2,
        new_elem < 0,
        new_elem >= -1000000
    ensures 
        old_sum + new_elem as i128 >= i128::MIN / 2,
        old_sum + new_elem as i128 <= i128::MAX / 2
{
}
// </vc-helpers>

// <vc-spec>
fn sum_negatives(arr: &Vec<i64>) -> (sum_neg: i128)
    // post-conditions-start
    ensures
        sum_negative_to(arr@) == sum_neg,
    // post-conditions-end
// </vc-spec>

// <vc-code>
{
    let mut sum_neg: i128 = 0;
    let mut i: usize = 0;
    
    while i < arr.len()
        invariant 
            0 <= i <= arr.len(),
            sum_neg == sum_negative_to(arr@.subrange(0, i as int)),
            sum_neg <= i128::MAX / 2,
            sum_neg >= i128::MIN / 2
        decreases arr.len() - i
    {
        if arr[i] < 0 {
            sum_neg = sum_neg + arr[i] as i128;
        }
        
        i = i + 1;
        
        proof {
            sum_negative_to_increment(arr@, (i-1) as int);
            if arr[(i-1) as int] < 0 {
                sum_bounds_preserved(old(sum_neg), arr[(i-1) as int]);
            }
        }
    }
    
    proof {
        assert(arr@.subrange(0, i as int) == arr@);
    }
    
    sum_neg
}
// </vc-code>

} // verus!

fn main() {}