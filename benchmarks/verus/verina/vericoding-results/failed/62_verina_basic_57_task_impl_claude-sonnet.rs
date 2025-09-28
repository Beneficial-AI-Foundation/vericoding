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
/* helper modified by LLM (iteration 5): Fixed missing closing brace */
proof fn count_spec_recursive_lemma(numbers: Seq<i32>, threshold: i32)
    requires
        numbers.len() > 0,
    ensures
        count_less_than_spec(numbers, threshold) == 
            if numbers[0] < threshold {
                1 + count_less_than_spec(numbers.subrange(1, numbers.len() as int), threshold)
            } else {
                count_less_than_spec(numbers.subrange(1, numbers.len() as int), threshold)
            },
{
    // This follows directly from the definition of count_less_than_spec
}

proof fn count_extension_lemma(numbers: Seq<i32>, threshold: i32, i: int)
    requires
        0 <= i < numbers.len(),
    ensures
        count_less_than_spec(numbers.subrange(0, i + 1), threshold) == 
            if numbers[i] < threshold {
                count_less_than_spec(numbers.subrange(0, i), threshold) + 1
            } else {
                count_less_than_spec(numbers.subrange(0, i), threshold)
            },
    decreases i
{
    let prefix = numbers.subrange(0, i);
    let extended = numbers.subrange(0, i + 1);
    
    if i == 0 {
        assert(prefix =~= Seq::<i32>::empty());
        assert(count_less_than_spec(prefix, threshold) == 0);
        assert(extended.len() == 1);
        assert(extended[0] == numbers[0]);
        count_spec_recursive_lemma(extended, threshold);
    } else {
        // Use the recursive structure to build up the proof
        let head = numbers[0];
        let tail_numbers = numbers.subrange(1, numbers.len() as int);
        let tail_prefix = tail_numbers.subrange(0, i - 1);
        let tail_extended = tail_numbers.subrange(0, i);
        
        count_extension_lemma(tail_numbers, threshold, i - 1);
        count_spec_recursive_lemma(numbers, threshold);
        count_spec_recursive_lemma(extended, threshold);
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
    /* code modified by LLM (iteration 5): Using extension lemma for precise proof */
    let mut count: usize = 0;
    let mut i: usize = 0;
    
    while i < numbers.len()
        invariant
            0 <= i <= numbers.len(),
            count == count_less_than_spec(numbers@.subrange(0, i as int), threshold),
            count <= i,
        decreases numbers.len() - i
    {
        if numbers[i] < threshold {
            proof {
                count_extension_lemma(numbers@, threshold, i as int);
            }
            count = count + 1;
        } else {
            proof {
                count_extension_lemma(numbers@, threshold, i as int);
            }
        }
        i = i + 1;
    }
    
    proof {
        assert(numbers@.subrange(0, numbers.len() as int) =~= numbers@);
    }
    
    count
}
// </vc-code>

}
fn main() {}