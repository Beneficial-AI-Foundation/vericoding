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
/* helper modified by LLM (iteration 5): Added a lemma to prove the count of elements less than a threshold in a subrange of a sequence. */
proof fn lemma_count_less_than_subrange(numbers: Seq<i32>, threshold: i32, i: int, j: int)
    requires
        0 <= i <= j <= numbers.len(),
    ensures
        count_less_than_spec(numbers.subrange(0, j), threshold) ==
        count_less_than_spec(numbers.subrange(0, i), threshold) +
        count_less_than_spec(numbers.subrange(i, j), threshold),
    decreases j - i
{
    if i < j {
        let first_in_subrange = numbers[i];
        let rest_of_subrange = numbers.subrange(i + 1, j);
        if first_in_subrange < threshold {
            assert(count_less_than_spec(numbers.subrange(i, j), threshold) == 1 + count_less_than_spec(rest_of_subrange, threshold));
            lemma_count_less_than_subrange(numbers, threshold, i + 1, j);
            assert(count_less_than_spec(numbers.subrange(0, j), threshold) == count_less_than_spec(numbers.subrange(0, i), threshold) + 1 + count_less_than_spec(rest_of_subrange, threshold));
        } else {
            assert(count_less_than_spec(numbers.subrange(i, j), threshold) == count_less_than_spec(rest_of_subrange, threshold));
            lemma_count_less_than_subrange(numbers, threshold, i + 1, j);
            assert(count_less_than_spec(numbers.subrange(0, j), threshold) == count_less_than_spec(numbers.subrange(0, i), threshold) + count_less_than_spec(rest_of_subrange, threshold));
        }
    }
}
// </vc-helpers>

// <vc-spec>
fn count_less_than(numbers: &Vec<i32>, threshold: i32) -> (result: usize)
    ensures
        result == count_less_than_spec(numbers@, threshold),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Added a proof block to justify the invariant update using the helper lemma and corrected potential overflow for `count`. */
{
    let mut count: usize = 0;
    let mut i: usize = 0;

    while i < numbers.len()
        invariant
            i <= numbers.len(),
            count == count_less_than_spec(numbers@.subrange(0, i as int), threshold) as usize,
            count <= numbers.len(),
        decreases numbers.len() - i
    {
        let at_i = numbers@[i];
        if at_i < threshold {
            proof {
                lemma_count_less_than_subrange(numbers@, threshold, i as int, (i + 1) as int);
                assert(count_less_than_spec(numbers@.subrange(0, (i + 1) as int), threshold) == 
                       count_less_than_spec(numbers@.subrange(0, i as int), threshold) + 1);
            }
            count = count + 1;
        } else {
            proof {
                lemma_count_less_than_subrange(numbers@, threshold, i as int, (i + 1) as int);
                assert(count_less_than_spec(numbers@.subrange(0, (i + 1) as int), threshold) == 
                       count_less_than_spec(numbers@.subrange(0, i as int), threshold));
            }
        }
        i = i + 1;
    }
    
    proof {
        lemma_count_less_than_subrange(numbers@, threshold, 0, numbers.len() as int);
    }
    count
}
// </vc-code>

}
fn main() {}