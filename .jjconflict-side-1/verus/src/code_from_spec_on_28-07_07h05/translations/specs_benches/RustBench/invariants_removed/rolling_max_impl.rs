use vstd::prelude::*;

verus! {

/* code modified by LLM (iteration 3): fixed seq_max definition to handle both cases correctly */
spec fn seq_max(a: Seq<i32>) -> i32
    decreases a.len(),
{
    if a.len() == 0 {
        i32::MIN
    } else if a.len() == 1 {
        a.last()
    } else {
        let rest_max = seq_max(a.drop_last());
        if a.last() > rest_max {
            a.last()
        } else {
            rest_max
        }
    }
}

/* code modified by LLM (iteration 3): added base case lemma for single element sequences */
proof fn lemma_seq_max_single(s: Seq<i32>)
    requires s.len() == 1
    ensures seq_max(s) == s[0]
{
    assert(s.last() == s[0]);
}

/* code modified by LLM (iteration 3): added helper lemma to connect iterative and recursive max computation */
proof fn lemma_seq_max_extend(s: Seq<i32>, elem: i32)
    requires s.len() > 0
    ensures seq_max(s.push(elem)) == if elem > seq_max(s) { elem } else { seq_max(s) }
    decreases s.len()
{
    let extended = s.push(elem);
    assert(extended.last() == elem);
    assert(extended.drop_last() == s);
    
    if extended.len() == 1 {
        assert(seq_max(extended) == elem);
        assert(s.len() == 0);
        assert(seq_max(s) == i32::MIN);
        assert(elem > seq_max(s));
    } else {
        let rest_max = seq_max(extended.drop_last());
        assert(rest_max == seq_max(s));
        
        if elem > rest_max {
            assert(seq_max(extended) == elem);
        } else {
            assert(seq_max(extended) == rest_max);
            assert(seq_max(extended) == seq_max(s));
        }
    }
}

/* code modified by LLM (iteration 3): added lemma to establish that take preserves max property */
proof fn lemma_take_properties(s: Seq<i32>, i: int)
    requires 0 < i < s.len()
    ensures s.take(i + 1) == s.take(i).push(s[i])
{
    let left = s.take(i + 1);
    let right = s.take(i).push(s[i]);
    
    assert(left.len() == right.len());
    assert forall |j: int| 0 <= j < left.len() implies left[j] == right[j] by {
        if j < i {
            assert(left[j] == s[j]);
            assert(right[j] == s.take(i)[j]);
            assert(s.take(i)[j] == s[j]);
        } else {
            assert(j == i);
            assert(left[j] == s[i]);
            assert(right[j] == s[i]);
        }
    }
}

fn rolling_max(numbers: Vec<i32>) -> (result: Vec<i32>)
    ensures
        result.len() == numbers.len(),
        forall|i: int| 0 <= i < numbers.len() ==> result[i] == seq_max(numbers@.take(i + 1)),
{
    let mut result = Vec::new();
    let mut current_max = i32::MIN;
    
    for i in 0..numbers.len()
        invariant
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result[j] == seq_max(numbers@.take(j + 1)),
            i > 0 ==> current_max == seq_max(numbers@.take(i as int)),
    {
        if i == 0 {
            current_max = numbers[0];
        } else {
            if numbers[i] > current_max {
                current_max = numbers[i];
            }
        }
        
        /* code modified by LLM (iteration 3): restructured proof with proper lemma applications */
        assert(current_max == seq_max(numbers@.take(i + 1))) by {
            if i == 0 {
                let single_seq = numbers@.take(1);
                assert(single_seq.len() == 1);
                assert(single_seq[0] == numbers[0]);
                lemma_seq_max_single(single_seq);
                assert(seq_max(single_seq) == numbers[0]);
                assert(current_max == numbers[0]);
            } else {
                let prev_seq = numbers@.take(i as int);
                let curr_seq = numbers@.take((i + 1) as int);
                
                lemma_take_properties(numbers@, i as int);
                assert(curr_seq == prev_seq.push(numbers[i as int]));
                
                // From loop invariant, we know current_max was seq_max(prev_seq) before this iteration
                let old_max = seq_max(prev_seq);
                
                lemma_seq_max_extend(prev_seq, numbers[i as int]);
                
                if numbers[i as int] > old_max {
                    assert(seq_max(curr_seq) == numbers[i as int]);
                    assert(current_max == numbers[i as int]); // from assignment in if branch
                } else {
                    assert(seq_max(curr_seq) == old_max);
                    assert(current_max == old_max); // current_max unchanged
                }
            }
        }
        
        result.push(current_max);
    }
    
    result
}

fn main() {}
}