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
/* helper modified by LLM (iteration 5): lemma to unfold count_less_than_spec for non-empty sequence */
proof fn count_less_than_unfold(rem: Seq<i32>, threshold: i32)
    requires rem.len() > 0
    ensures count_less_than_spec(rem, threshold) == if rem@[0] < threshold { 1 + count_less_than_spec(rem.subrange(1, rem.len() as int), threshold) } else { count_less_than_spec(rem.subrange(1, rem.len() as int), threshold) }
{
    proof {
        assert(count_less_than_spec(rem, threshold) == if rem@[0] < threshold { 1 + count_less_than_spec(rem.subrange(1, rem.len() as int), threshold) } else { count_less_than_spec(rem.subrange(1, rem.len() as int), threshold) });
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
    /* code modified by LLM (iteration 5): correct iterative implementation with usize indices and invariants */
    let s = numbers@;
    let total: nat = count_less_than_spec(s, threshold);
    let n: usize = numbers.len();
    let mut i: usize = 0;
    let mut acc: nat = 0;
    while i < n
        invariant i <= n;
        invariant acc + count_less_than_spec(s.subrange(i as int, n as int), threshold) == total;
        decreases n - i;
    {
        let v = numbers[i];
        let rem = s.subrange(i as int, n as int);
        let old_acc = acc;
        if v < threshold {
            acc = acc + 1;
        }
        i = i + 1;
        proof {
            count_less_than_unfold(rem, threshold);
            assert(old_acc + count_less_than_spec(rem, threshold) == total);
            assert(rem@[0] == v);
            if rem@[0] < threshold {
                assert(old_acc + 1 + count_less_than_spec(rem.subrange(1, rem.len() as int), threshold) == total);
            } else {
                assert(old_acc + count_less_than_spec(rem.subrange(1, rem.len() as int), threshold) == total);
            }
            assert(acc == if rem@[0] < threshold { old_acc + 1 } else { old_acc });
            assert(acc + count_less_than_spec(rem.subrange(1, rem.len() as int), threshold) == total);
        }
    }
    acc as usize
}
// </vc-code>

}
fn main() {}