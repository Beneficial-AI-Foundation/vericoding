// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
proof fn lemma_sum_range_zero(a: Seq<i32>, start: int)
    ensures
        sum_range(a, start, 0) == 0,
{
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
    let mut i: usize = start;
    let mut acc: i32 = 0;
    while i < finish
        invariant
            start <= i,
            i <= finish,
            finish <= a.len(),
            acc as int + sum_range(a@, i as int, finish as int - i as int) ==
                sum_range(a@, start as int, finish as int - start as int),
        decreases finish as int - i as int
    {
        proof {
            assert(finish as int - i as int > 0);
            assert(sum_range(a@, i as int, finish as int - i as int)
                == a@[i as int] + sum_range(a@, i as int + 1, finish as int - i as int - 1));
        }
        acc = acc + a[i];
        i = i + 1;
    }
    acc
}

// </vc-code>


}
fn main() {}