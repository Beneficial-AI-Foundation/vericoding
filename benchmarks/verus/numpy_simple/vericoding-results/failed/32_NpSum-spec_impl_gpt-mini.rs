// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): lemma that sum_range(a,s,len) == sum_range(a,s,len-1) + a[s+len-1] */
fn sum_range_snoc(a: Seq<i32>, s: int, len: int)
    requires 0 <= s, 0 < len, s + len <= a.len(),
    ensures sum_range(a, s, len) == sum_range(a, s, len - (1 as int)) + a[s + len - (1 as int)],
    decreases len
{
    if len == (1 as int) {
        proof {
            assert(sum_range(a, s, 1 as int) == a[s] + sum_range(a, s + 1 as int, 0 as int));
            assert(sum_range(a, s, 0 as int) == 0);
            assert(a[s] + sum_range(a, s + 1 as int, 0 as int) == sum_range(a, s, 0 as int) + a[s + 1 as int - 1 as int]);
            assert(sum_range(a, s, 1 as int) == sum_range(a, s, 0 as int) + a[s + 1 as int - 1 as int]);
        }
    } else {
        sum_range_snoc(a, s + 1 as int, len - (1 as int));
        proof {
            assert(sum_range(a, s, len) == a[s] + sum_range(a, s + 1 as int, len - (1 as int)));
            assert(sum_range(a, s, len - (1 as int)) == a[s] + sum_range(a, s + 1 as int, len - (2 as int)));
            assert(sum_range(a, s + 1 as int, len - (1 as int)) == sum_range(a, s + 1 as int, len - (2 as int)) + a[s + len - (1 as int)]);
            assert(a[s] + sum_range(a, s + 1 as int, len - (1 as int)) == a[s] + (sum_range(a, s + 1 as int, len - (2 as int)) + a[s + len - (1 as int)]));
            assert(a[s] + (sum_range(a, s + 1 as int, len - (2 as int)) + a[s + len - (1 as int)]) == (a[s] + sum_range(a, s + 1 as int, len - (2 as int))) + a[s + len - (1 as int)]);
            assert((a[s] + sum_range(a, s + 1 as int, len - (2 as int))) + a[s + len - (1 as int)] == sum_range(a, s, len - (1 as int)) + a[s + len - (1 as int)]);
            assert(sum_range(a, s, len) == sum_range(a, s, len - (1 as int)) + a[s + len - (1 as int)]);
        }
    }
}

// </vc-helpers>

// <vc-spec>
spec fn sum_range(a: Seq<i32>, start: int, len: int) -> int
    decreases len
{
    if len <= 0 || start < 0 || start + len > a.len() {
        0
    } else if len == 0 {
        0
    } else {
        a[start] + sum_range(a, start + 1, len - 1)
    }
}

spec fn seq_sum(a: Seq<i32>) -> int {
    sum_range(a, 0, a.len() as int)
}

fn sum(a: Vec<i32>) -> (result: i32)
    ensures result == seq_sum(a@)
{
    // impl-start
    assume(false);
    unreached()
    // impl-end
}

fn sum_array(a: Vec<i32>, start: usize, finish: usize) -> (result: i32)
    requires start <= finish, finish <= a.len(),
    ensures result == sum_range(a@, start as int, (finish - start) as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): iterative sum_array with invariant and lemma use */
    let mut i: usize = start;
    let mut acc: i32 = 0;
    while i < finish
        invariant
            start <= i,
            i <= finish,
            acc == sum_range(a@, start as int, (i - start) as int),
        decreases finish - i
    {
        let ai: i32 = a[i];
        proof {
            // show lemma preconditions
            assert(0 <= start as int);
            assert((i + 1 - start) as int > 0);
            assert(start as int + (i + 1 - start) as int <= a@.len());
            sum_range_snoc(a@, start as int, (i + 1 - start) as int);
            assert(acc == sum_range(a@, start as int, (i - start) as int));
            assert(a@[i as int] == ai);
            assert(acc + a@[i as int] == sum_range(a@, start as int, (i + 1 - start) as int));
        }
        acc = acc + ai;
        i = i + 1;
    }
    acc
}

// </vc-code>


}
fn main() {}