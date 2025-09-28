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
/* helper modified by LLM (iteration 5): Fixed lemma to properly prove count split relationship */
proof fn lemma_count_split(numbers: Seq<i32>, threshold: i32, i: int)
    requires
        0 <= i <= numbers.len(),
    ensures
        count_less_than_spec(numbers, threshold) == count_less_than_spec(numbers.subrange(0, i), threshold) + count_less_than_spec(numbers.subrange(i, numbers.len() as int), threshold),
    decreases numbers.len() - i
{
    if i == 0 {
        assert(numbers.subrange(0, 0).len() == 0);
        assert(count_less_than_spec(numbers.subrange(0, 0), threshold) == 0);
        assert(numbers.subrange(0, numbers.len() as int) == numbers);
    } else if i == numbers.len() {
        assert(numbers.subrange(0, i) == numbers);
        assert(numbers.subrange(i, numbers.len() as int).len() == 0);
        assert(count_less_than_spec(numbers.subrange(i, numbers.len() as int), threshold) == 0);
    } else {
        // Prove by induction
        lemma_count_split(numbers.subrange(1, numbers.len() as int), threshold, i - 1);
        
        // Key insight: numbers = [numbers[0]] + numbers.subrange(1, len)
        assert(numbers.subrange(0, 1).len() == 1);
        assert(numbers.subrange(0, 1)[0] == numbers[0]);
        
        if numbers[0] < threshold {
            assert(count_less_than_spec(numbers, threshold) == 1 + count_less_than_spec(numbers.subrange(1, numbers.len() as int), threshold));
        } else {
            assert(count_less_than_spec(numbers, threshold) == count_less_than_spec(numbers.subrange(1, numbers.len() as int), threshold));
        }
    }
}

proof fn lemma_count_append_one(numbers: Seq<i32>, threshold: i32, value: i32)
    ensures
        count_less_than_spec(numbers.push(value), threshold) == 
            if value < threshold { 
                count_less_than_spec(numbers, threshold) + 1 
            } else { 
                count_less_than_spec(numbers, threshold) 
            },
    decreases numbers.len()
{
    if numbers.len() == 0 {
        assert(numbers.push(value).len() == 1);
        assert(numbers.push(value)[0] == value);
    } else {
        lemma_count_append_one(numbers.subrange(1, numbers.len() as int), threshold, value);
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
    /* code modified by LLM (iteration 5): Simplified loop with better invariant reasoning */
    let mut count: usize = 0;
    let mut i: usize = 0;
    
    while i < numbers.len()
        invariant
            0 <= i <= numbers.len(),
            count == count_less_than_spec(numbers@.subrange(0, i as int), threshold),
            count <= i,
        decreases numbers.len() - i
    {
        let old_count = count;
        let old_i = i;
        
        if numbers[i] < threshold {
            count = count + 1;
        }
        
        proof {
            // Prove the invariant is maintained
            assert(numbers@.subrange(0, (old_i + 1) as int).len() == old_i + 1);
            
            // Key: numbers@.subrange(0, i+1) = numbers@.subrange(0, i).push(numbers[i])
            assert(numbers@.subrange(0, (old_i + 1) as int) == numbers@.subrange(0, old_i as int).push(numbers@[old_i as int]));
            
            // Use the append lemma
            lemma_count_append_one(numbers@.subrange(0, old_i as int), threshold, numbers@[old_i as int]);
        }
        
        i = i + 1;
    }
    
    proof {
        assert(i == numbers.len());
        assert(numbers@.subrange(0, i as int) == numbers@);
    }
    
    count
}
// </vc-code>

}
fn main() {}