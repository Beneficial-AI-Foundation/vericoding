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
proof fn sum_negative_to_monotonic(seq: Seq<i64>, i: nat)
    requires i < seq.len()
    ensures sum_negative_to(seq.take(i as int)) + (if seq[i as int] < 0 { seq[i as int] as int } else { 0 }) == sum_negative_to(seq.take((i + 1) as int))
    decreases seq.len() - i
{
    let prefix_i = seq.take(i as int);
    let prefix_i_plus_1 = seq.take((i + 1) as int);
    
    if i == 0 {
        assert(prefix_i.len() == 0);
        assert(prefix_i_plus_1.len() == 1);
        assert(prefix_i_plus_1[0] == seq[0]);
    } else {
        assert(prefix_i_plus_1 == prefix_i.push(seq[i as int]));
        assert(prefix_i_plus_1.drop_last() == prefix_i);
        assert(prefix_i_plus_1.last() == seq[i as int]);
    }
}

proof fn sum_negative_to_take_all(seq: Seq<i64>)
    ensures sum_negative_to(seq.take(seq.len() as int)) == sum_negative_to(seq)
{
    assert(seq.take(seq.len() as int) == seq);
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
            i <= arr.len(),
            sum_neg == sum_negative_to(arr@.take(i as int)),
        decreases arr.len() - i
    {
        if arr[i] < 0 {
            sum_neg = sum_neg + arr[i] as i128;
        }
        
        proof {
            sum_negative_to_monotonic(arr@, i as nat);
        }
        
        i = i + 1;
    }
    
    proof {
        sum_negative_to_take_all(arr@);
    }
    
    sum_neg
}
// </vc-code>

} // verus!

fn main() {}