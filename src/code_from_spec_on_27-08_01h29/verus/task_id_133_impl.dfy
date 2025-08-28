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
proof fn lemma_sum_negative_to_add_positive(seq: Seq<i64>, x: i64)
    requires x >= 0
    ensures sum_negative_to(seq.push(x)) == sum_negative_to(seq)
{
    assert(seq.push(x).last() == x);
    assert(seq.push(x).drop_last() == seq);
}

proof fn lemma_sum_negative_to_add_negative(seq: Seq<i64>, x: i64)
    requires x < 0
    ensures sum_negative_to(seq.push(x)) == sum_negative_to(seq) + x as int
{
    assert(seq.push(x).last() == x);
    assert(seq.push(x).drop_last() == seq);
}

proof fn lemma_sum_negative_to_slice(seq: Seq<i64>, i: int)
    requires 0 <= i < seq.len()
    ensures sum_negative_to(seq.subrange(0, i + 1)) == 
            sum_negative_to(seq.subrange(0, i)) + 
            if seq[i] < 0 { seq[i] as int } else { 0 as int }
{
    let s1 = seq.subrange(0, i + 1);
    let s2 = seq.subrange(0, i);
    assert(s1.len() == i + 1);
    assert(s2.len() == i);
    assert(s1.last() == seq[i]);
    assert(s1.drop_last() == s2);
}

proof fn lemma_sum_negative_bounds(seq: Seq<i64>)
    ensures sum_negative_to(seq) >= (seq.len() as int) * (i64::MIN as int)
    ensures sum_negative_to(seq) <= 0
    decreases seq.len()
{
    if seq.len() == 0 {
    } else {
        lemma_sum_negative_bounds(seq.drop_last());
    }
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
    
    proof {
        lemma_sum_negative_bounds(arr@);
    }
    
    while i < arr.len()
        invariant
            0 <= i <= arr.len(),
            sum_neg == sum_negative_to(arr@.subrange(0, i as int)),
            sum_neg >= (i as int) * (i64::MIN as int),
            sum_neg <= 0,
        decreases arr.len() - i
    {
        proof {
            lemma_sum_negative_to_slice(arr@, i as int);
        }
        
        if arr[i] < 0 {
            sum_neg = sum_neg + arr[i] as i128;
        }
        
        i = i + 1;
    }
    
    proof {
        assert(i == arr.len());
        assert(arr@.subrange(0, i as int) == arr@);
    }
    
    sum_neg
}
// </vc-code>

} // verus!

fn main() {}