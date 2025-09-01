use vstd::prelude::*;

verus! {

spec fn seq_max(a: Seq<i32>) -> (ret: i32)
    decreases a.len(),
{
    if a.len() == 0 {
        i32::MIN
    } else if a.last() > seq_max(a.drop_last()) {
        a.last()
    } else {
        seq_max(a.drop_last())
    }
}

// <vc-helpers>
proof fn lemma_seq_max_monotonic(a: Seq<i32>, b: Seq<i32>)
    requires
        a.len() > 0,
        b.len() > 0,
        a == b.drop_last(),
    ensures
        seq_max(b) >= seq_max(a),
    decreases b.len(),
{
    if b.len() == 1 {
        assert(a.len() == 0);
        assert(seq_max(a) == i32::MIN);
    } else {
        lemma_seq_max_monotonic(a.drop_last(), a);
    }
}

proof fn lemma_seq_max_last_element(a: Seq<i32>)
    requires a.len() > 0,
    ensures seq_max(a) >= a.last(),
    decreases a.len(),
{
    if a.len() == 1 {
        assert(seq_max(a) == a.last());
    } else {
        lemma_seq_max_last_element(a.drop_last());
        if a.last() > seq_max(a.drop_last()) {
            assert(seq_max(a) == a.last());
        } else {
            assert(seq_max(a) == seq_max(a.drop_last()));
            assert(seq_max(a.drop_last()) >= a.last());
        }
    }
}

proof fn lemma_seq_max_element(a: Seq<i32>, j: int)
    requires
        0 <= j < a.len(),
    ensures
        seq_max(a) >= a[j],
    decreases a.len(),
{
    if j == a.len() - 1 {
        lemma_seq_max_last_element(a);
    } else {
        lemma_seq_max_element(a.drop_last(), j);
        if a.last() > seq_max(a.drop_last()) {
            assert(seq_max(a) == a.last());
            assert(seq_max(a.drop_last()) >= a[j]);
            assert(a.last() > seq_max(a.drop_last()));
        } else {
            assert(seq_max(a) == seq_max(a.drop_last()));
        }
    }
}
// </vc-helpers>

// <vc-spec>
fn rolling_max(numbers: Vec<i32>) -> (result: Vec<i32>)
    // post-conditions-start
    ensures
        result.len() == numbers.len(),
        forall|i: int| 0 <= i < numbers.len() ==> result[i] == seq_max(numbers@.take(i + 1)),
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    let mut result = Vec::new();
    let mut current_max = i32::MIN;
    
    for i in 0..numbers.len()
        invariant
            result.len() == i,
            current_max == if i == 0 { i32::MIN } else { seq_max(numbers@.take(i as int)) },
            forall|j: int| 0 <= j < i ==> result[j] == seq_max(numbers@.take(j + 1)),
    {
        if i == 0 {
            current_max = numbers[i];
        } else {
            if numbers[i] > current_max {
                current_max = numbers[i];
            }
        }
        
        result.push(current_max);
        
        proof {
            let take_seq = numbers@.take((i + 1) as int);
            assert(take_seq.len() == i + 1);
            assert(take_seq.last() == numbers[i as int]);
            
            if i == 0 {
                assert(take_seq.len() == 1);
                assert(seq_max(take_seq) == take_seq.last());
                assert(current_max == numbers[i as int]);
            } else {
                let prev_take_seq = numbers@.take(i as int);
                assert(take_seq == prev_take_seq.push(numbers[i as int]));
                assert(take_seq.drop_last() == prev_take_seq);
                
                if numbers[i as int] > current_max {
                    assert(false);
                } else {
                    if numbers[i as int] > seq_max(prev_take_seq) {
                        assert(seq_max(take_seq) == numbers[i as int]);
                        assert(current_max == numbers[i as int]);
                    } else {
                        assert(seq_max(take_seq) == seq_max(prev_take_seq));
                        assert(current_max == seq_max(prev_take_seq));
                    }
                }
            }
        }
    }
    
    result
}
// </vc-code>

fn main() {}
}