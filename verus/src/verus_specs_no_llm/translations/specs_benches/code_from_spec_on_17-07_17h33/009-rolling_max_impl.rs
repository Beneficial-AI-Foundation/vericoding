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

/* code modified by LLM (iteration 2): Added helper lemma to prove seq_max properties */
proof fn seq_max_extend_lemma(a: Seq<i32>, x: i32)
    requires a.len() > 0
    ensures seq_max(a.push(x)) == if x > seq_max(a) { x } else { seq_max(a) }
{
    let extended = a.push(x);
    assert(extended.last() == x);
    assert(extended.drop_last() == a);
}

/* code modified by LLM (iteration 2): Added helper lemma for empty sequence */
proof fn seq_max_empty_lemma()
    ensures seq_max(Seq::<i32>::empty()) == i32::MIN
{
}

fn rolling_max(numbers: Vec<i32>) -> (result: Vec<i32>)
    ensures
        result.len() == numbers.len(),
        forall|i: int| 0 <= i < numbers.len() ==> result[i] == seq_max(numbers@.take(i + 1)),
{
    /* code modified by LLM (iteration 3): Reimplemented with proper tracking of current_max and type casting */
    let mut result = Vec::new();
    let mut current_max = i32::MIN;
    
    for i in 0..numbers.len()
        invariant
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result[j] == seq_max(numbers@.take(j + 1)),
            current_max == if i == 0 { i32::MIN } else { seq_max(numbers@.take(i as int)) },
    {
        /* code modified by LLM (iteration 3): Updated current_max calculation with proper proof and type casting */
        if i == 0 {
            current_max = numbers[i];
        } else {
            if numbers[i] > current_max {
                current_max = numbers[i];
            }
        }
        
        result.push(current_max);
        
        /* code modified by LLM (iteration 3): Added proper proof for the assertion with type casting */
        assert(current_max == seq_max(numbers@.take(i as int + 1))) by {
            let prefix = numbers@.take(i as int + 1);
            if i == 0 {
                assert(prefix.len() == 1);
                assert(prefix[0] == numbers[i as int]);
                assert(seq_max(prefix) == numbers[i as int]);
            } else {
                let prev_prefix = numbers@.take(i as int);
                seq_max_extend_lemma(prev_prefix, numbers[i as int]);
                assert(seq_max(prefix) == if numbers[i as int] > seq_max(prev_prefix) { numbers[i as int] } else { seq_max(prev_prefix) });
            }
        }
    }
    
    result
}

}
fn main() {}