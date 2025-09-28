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

// </vc-helpers>

// <vc-spec>
fn count_less_than(numbers: &Vec<i32>, threshold: i32) -> (result: usize)
    ensures
        result == count_less_than_spec(numbers@, threshold),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): changed count type to u64 to avoid overflow, added proofs for invariant */
    let mut count: u64 = 0;
    let mut i: usize = 0;
    while i < numbers.len()
        invariant
            i <= numbers.len(),
            count as nat == count_less_than_spec(numbers@.subrange(0, i as int), threshold),
        decreases numbers.len() - i
    {
        if numbers[i] < threshold {
            count = count + 1;
        }
        i = i + 1;
        proof {
            assert(count as nat == count_less_than_spec(numbers@.subrange(0, i as int), threshold));
        }
    }
    proof {
        assert(count as nat == count_less_than_spec(numbers@, threshold));
    }
    (count as usize)
}
// </vc-code>

}
fn main() {}