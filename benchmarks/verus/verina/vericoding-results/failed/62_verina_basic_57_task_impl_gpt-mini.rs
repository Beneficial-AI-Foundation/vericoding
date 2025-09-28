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
/* helper modified by LLM (iteration 5): lemma for count_less_than_spec over concatenation */
proof fn lemma_count_concat(xs: Seq<i32>, ys: Seq<i32>, thr: i32)
    ensures
        count_less_than_spec(xs + ys, thr) == count_less_than_spec(xs, thr) + count_less_than_spec(ys, thr)
    decreases
        xs.len()
{
    if xs.len() == 0 {
        assert(xs + ys == ys);
        assert(count_less_than_spec(xs + ys, thr) == count_less_than_spec(ys, thr));
    } else {
        let xs_len = xs.len();
        let head = xs[0];
        let tail = xs.subrange(1, xs_len);
        // induction on tail
        lemma_count_concat(tail, ys, thr);
        // relate lengths and subranges for concatenation
        assert((xs + ys).len() == xs_len + ys.len());
        assert((xs + ys).subrange(1, (xs + ys).len()) == tail + ys);
        if head < thr {
            // unfold definitions when head < thr
            assert(count_less_than_spec(xs + ys, thr) == 1 + count_less_than_spec(tail + ys, thr));
            assert(count_less_than_spec(xs, thr) == 1 + count_less_than_spec(tail, thr));
            assert(count_less_than_spec(tail + ys, thr) == count_less_than_spec(tail, thr) + count_less_than_spec(ys, thr));
            assert(count_less_than_spec(xs + ys, thr) == count_less_than_spec(xs, thr) + count_less_than_spec(ys, thr));
        } else {
            // unfold definitions when head >= thr
            assert(count_less_than_spec(xs + ys, thr) == count_less_than_spec(tail + ys, thr));
            assert(count_less_than_spec(xs, thr) == count_less_than_spec(tail, thr));
            assert(count_less_than_spec(tail + ys, thr) == count_less_than_spec(tail, thr) + count_less_than_spec(ys, thr));
            assert(count_less_than_spec(xs + ys, thr) == count_less_than_spec(xs, thr) + count_less_than_spec(ys, thr));
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
    /* code modified by LLM (iteration 5): iterative count using while loop with preserved invariants */
    let mut i: usize = 0;
    let mut cnt: usize = 0;
    let n: usize = numbers.len();
    proof {
        // relate runtime and spec lengths
        assert(n == numbers.len());
        assert(n as int == numbers@.len());
    }
    while i < n
        invariant
            i <= n,
            cnt <= n,
            cnt == count_less_than_spec(numbers@.subrange(0, i as int), threshold),
        decreases
            n - i
    {
        let v = numbers[i];
        if v < threshold {
            cnt = cnt + 1;
        }
        i = i + 1;
    }
    proof {
        // at loop end i == n, relate subrange to full sequence
        assert(cnt == count_less_than_spec(numbers@.subrange(0, n as int), threshold));
        assert(numbers@.subrange(0, n as int) == numbers@);
    }
    cnt
}

// </vc-code>

}
fn main() {}