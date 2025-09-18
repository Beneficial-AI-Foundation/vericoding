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
/* helper modified by LLM (iteration 5): relate subrange head to recursive spec */
proof fn lemma_subrange_head(s: Seq<i32>, i: usize, n: usize, threshold: i32)
    requires
        i < n,
        n <= s.len(),
    ensures
        count_less_than_spec(s.subrange(i as int, n as int), threshold) == (if s[i] < threshold { 1usize } else { 0usize }) + count_less_than_spec(s.subrange((i+1) as int, n as int), threshold),
{
    reveal(count_less_than_spec);
    let s1 = s.subrange(i as int, n as int);
    assert(s1.len() == n - i);
    assert(s1.len() > 0);
    let first = s1[0];
    let rest = s1.subrange(1, s1.len() as int);
    assert(first == s[i]);
    assert(rest == s.subrange((i+1) as int, n as int));
    assert(count_less_than_spec(s1, threshold) ==
        if first < threshold { 1usize + count_less_than_spec(rest, threshold) } else { count_less_than_spec(rest, threshold) });
}

// </vc-helpers>

// <vc-spec>
fn count_less_than(numbers: &Vec<i32>, threshold: i32) -> (result: usize)
    ensures
        result == count_less_than_spec(numbers@, threshold),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): loop counting elements less than threshold using runtime indexing and helper lemma */
    let n = numbers.len();
    let mut i: usize = 0;
    let mut acc: usize = 0;
    while i < n
        invariant
            i <= n,
            (acc as int) + count_less_than_spec((numbers@).subrange(i as int, n as int), threshold) == count_less_than_spec(numbers@, threshold),
        decreases n - i
    {
        let old_i = i;
        let old_acc = acc;
        let v = numbers[old_i];
        proof {
            lemma_subrange_head(numbers@, old_i, n, threshold);
            assert(count_less_than_spec((numbers@).subrange(old_i as int, n as int), threshold) ==
                (if v < threshold { 1usize } else { 0usize }) + count_less_than_spec((numbers@).subrange((old_i as int) + 1, n as int), threshold));
        }
        if v < threshold {
            acc = acc + 1;
        }
        i = i + 1;
        proof {
            if v < threshold {
                assert((acc as int) == (old_acc as int) + 1);
            } else {
                assert((acc as int) == (old_acc as int));
            }
            assert((acc as int) + count_less_than_spec((numbers@).subrange(i as int, n as int), threshold) == count_less_than_spec(numbers@, threshold));
        }
    }
    acc
}

// </vc-code>

}
fn main() {}