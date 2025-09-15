// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn count_less_than_spec(numbers: Seq<i32>, threshold: i32) -> nat
    decreases numbers.len()
{
    if numbers.len() == 0 {
        0
    } else {
        let first = numbers[0];
        let rest = numbers.subrange(1, numbers.len() as int);
        if first < threshold {
            1 + count_less_than_spec(rest, threshold)
        } else {
            count_less_than_spec(rest, threshold)
        }
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fix lemma to prove invariant step */
proof fn count_less_than_step_lemma(numbers: Seq<i32>, threshold: i32, i: nat)
    requires i < numbers.len()
    ensures 
        count_less_than_spec(numbers.subrange(0, (i + 1) as int), threshold) == 
        if numbers[i as int] < threshold {
            count_less_than_spec(numbers.subrange(0, i as int), threshold) + 1
        } else {
            count_less_than_spec(numbers.subrange(0, i as int), threshold)
        }
{
    let prev_subrange = numbers.subrange(0, i as int);
    let curr_subrange = numbers.subrange(0, (i + 1) as int);
    assert(curr_subrange == prev_subrange.push(numbers[i as int]));
    
    if i == 0 {
        assert(prev_subrange == Seq::<i32>::empty());
        assert(count_less_than_spec(prev_subrange, threshold) == 0);
    }
}
// </vc-helpers>

// <vc-spec>
fn count_less_than(numbers: &Vec<i32>, threshold: i32) -> (result: usize)
    ensures
        result == count_less_than_spec(numbers@, threshold),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): use step lemma to prove invariant */
    let mut count = 0usize;
    let mut i = 0usize;
    
    while i < numbers.len()
        invariant
            i <= numbers.len(),
            count == count_less_than_spec(numbers@.subrange(0, i as int), threshold)
        decreases numbers.len() - i
    {
        proof {
            count_less_than_step_lemma(numbers@, threshold, i as nat);
        }
        
        if numbers[i] < threshold {
            count = count + 1;
        }
        i = i + 1;
    }
    
    proof {
        assert(numbers@.subrange(0, i as int) == numbers@);
    }
    
    count
}
// </vc-code>

}
fn main() {}