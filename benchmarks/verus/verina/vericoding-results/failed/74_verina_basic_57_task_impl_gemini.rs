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
proof fn lemma_count_spec_append(s1: Seq<i32>, s2: Seq<i32>, threshold: i32)
    ensures
        count_less_than_spec(s1 + s2, threshold) == count_less_than_spec(s1, threshold) + count_less_than_spec(s2, threshold),
    decreases s1.len()
{
    if s1.len() > 0 {
        lemma_count_spec_append(s1.subrange(1, s1.len() as int), s2, threshold);
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
    let mut count: usize = 0;
    let mut i: usize = 0;
    while i < numbers.len()
        invariant
            0 <= i <= numbers.len(),
            count == count_less_than_spec(numbers@.subrange(0, i as int), threshold),
    {
        proof {
            let s = numbers@;
            let i_int = i as int;
            lemma_count_spec_append(s.subrange(0, i_int), s.subrange(i_int, i_int + 1), threshold);
        }

        if numbers[i] < threshold {
            count = count + 1;
        }
        i = i + 1;
    }
    count
}
// </vc-code>

}
fn main() {}