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
/* helper modified by LLM (iteration 3): added lemma to bound the count */
proof fn lemma_count_bound(s: Seq<i32>, t: i32)
    ensures
        count_less_than_spec(s, t) <= s.len(),
    decreases s.len(),
{
    if s.len() > 0 {
        lemma_count_bound(s.subrange(1, s.len() as int), t);
    }
}

/* helper modified by LLM (iteration 4): added assertions to help verus with sequence arithmetic */
proof fn lemma_count_split(s: Seq<i32>, t: i32, i: int)
    requires
        0 <= i <= s.len(),
    ensures
        count_less_than_spec(s, t) ==
            count_less_than_spec(s.subrange(0, i), t) + count_less_than_spec(s.subrange(i, s.len() as int), t),
    decreases s.len(),
{
    if s.len() > 0 && i > 0 {
        let s_rest = s.subrange(1, s.len() as int);
        let i_rest = i - 1;
        lemma_count_split(s_rest, t, i_rest);

        assert(s_rest.subrange(0, i_rest) === s.subrange(1, i));
        assert(s_rest.subrange(i_rest, s_rest.len() as int) === s.subrange(i, s.len() as int));
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
    /* code modified by LLM (iteration 4): moved proof calls into proof blocks */
    let mut i: usize = 0;
    let mut count: usize = 0;
    while i < numbers.len()
        invariant
            0 <= i <= numbers.len(),
            count as nat == count_less_than_spec(numbers@.subrange(0, i as int), threshold),
            numbers@.len() < usize::MAX ==> i < usize::MAX,
        decreases numbers.len() - i
    {
        proof {
            lemma_count_bound(numbers@.subrange(0, i as int), threshold);
        }

        let num = numbers[i];
        
        if num < threshold {
            count = count + 1;
        }

        proof {
            lemma_count_split(numbers@.subrange(0, (i + 1) as int), threshold, i as int);
        }

        i = i + 1;
    }
    count
}
// </vc-code>

}
fn main() {}