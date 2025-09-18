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
/* helper modified by LLM (iteration 5): fixed proof structure to properly handle recursive decomposition and termination */
proof fn count_less_than_rec_lemma(numbers: Seq<i32>, threshold: i32, i: nat)
    requires
        i <= numbers.len(),
    ensures
        count_less_than_spec(numbers, threshold) == count_less_than_spec(numbers.subrange(0, i as int), threshold) + count_less_than_spec(numbers.subrange(i as int, numbers.len() as int), threshold),
    decreases i
{
    if i == 0 {
        assert(numbers.subrange(0, 0) =~= Seq::<i32>::empty());
        assert(numbers.subrange(0, numbers.len() as int) =~= numbers);
    } else if i == numbers.len() {
        assert(numbers.subrange(numbers.len() as int, numbers.len() as int) =~= Seq::<i32>::empty());
        assert(numbers.subrange(0, numbers.len() as int) =~= numbers);
    } else {
        count_less_than_rec_lemma(numbers, threshold, i - 1);
        let elem = numbers[i - 1];
        let left_part = numbers.subrange(0, (i - 1) as int);
        let mid_elem = numbers.subrange((i - 1) as int, i as int);
        let right_part = numbers.subrange(i as int, numbers.len() as int);
        assert(numbers.subrange(0, i as int) =~= left_part + mid_elem);
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
    /* code modified by LLM (iteration 5): fixed count type to prevent overflow and properly maintain invariant */
    let mut count: usize = 0;
    let mut i: usize = 0;
    
    while i < numbers.len()
        invariant
            i <= numbers.len(),
            count == count_less_than_spec(numbers@.subrange(0, i as int), threshold),
            count <= i,
        decreases numbers.len() - i
    {
        if numbers[i] < threshold {
            count = count + 1;
        }
        i = i + 1;
    }
    
    proof {
        assert(numbers@.subrange(0, i as int) =~= numbers@);
    }
    
    count
}
// </vc-code>

}
fn main() {}