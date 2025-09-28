// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): [explicit proof steps for sum split lemma] */
proof fn lemma_sum_range_split(a: Seq<i32>, start: int, len: int)
    requires
        start >= 0,
        len >= 0,
        start + len < a.len(),
    ensures
        sum_range(a, start, len + 1) == sum_range(a, start, len) + a[start + len],
    decreases len
{
    if len > 0 {
        lemma_sum_range_split(a, start + 1, len - 1);
        calc! {
            (==)
            sum_range(a, start, len) + a[start + len];
            (a[start] + sum_range(a, start + 1, len - 1)) + a[start + len];
            a[start] + (sum_range(a, start + 1, len - 1) + a[start + len]);
            a[start] + sum_range(a, start + 1, len);
            sum_range(a, start, len + 1);
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
    /* code modified by LLM (iteration 5): [add preconditions for overflow, fix lemma call] */
    let mut s: i32 = 0;
    let mut i: usize = start;
    while i < finish
        invariant
            start <= i <= finish,
            s as int == sum_range(a@, start as int, (i - start) as int),
            forall|j: int| start <= j < i ==> i32::MIN <= sum_range(a@, start as int, j - start + 1) <= i32::MAX,
        decreases finish - i
    {
        assert(i < a.len()); // prove precondition for a[i] and for the lemma
        proof {
            let current_len = (i - start) as int;
            if current_len >= 0 {
                lemma_sum_range_split(a@, start as int, current_len);
            }
        }
        s = s + a[i];
        i = i + 1;
    }
    s
}
// </vc-code>


}
fn main() {}