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
proof fn count_less_than_iter(numbers: &Vec<i32>, threshold: i32, n: nat) -> (count: nat)
    requires
        n <= numbers.len(),
    ensures
        count == count_less_than_spec(numbers@.subrange(0, n as int), threshold),
    decreases n
{
    if n == 0 {
        0
    } else {
        let prev = count_less_than_iter(numbers, threshold, (n - 1) as nat);
        assert(numbers[n - 1] == numbers@[n - 1]);
        if numbers[n - 1] < threshold {
            prev + 1
        } else {
            prev
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
{
    /* code modified by LLM (iteration 5): Fixed arithmetic overflow and loop invariant */
    let mut index: usize = 0;
    let mut count: usize = 0;
    
    while index < numbers.len()
        invariant
            count as nat == count_less_than_spec(numbers@.subrange(0, index as int), threshold),
            index <= numbers.len(),
        decreases numbers.len() - index
    {
        if numbers[index] < threshold {
            count = count + 1;
        }
        index = index + 1;
    }
    count
}
// </vc-code>

}
fn main() {}