// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
proof fn sum_range_empty(a: Seq<i32>, start: int)
    ensures
        sum_range(a, start, 0) == 0
{
}

proof fn sum_range_single(a: Seq<i32>, start: int)
    requires
        0 <= start < a.len()
    ensures
        sum_range(a, start, 1) == a[start]
{
}

proof fn sum_range_split(a: Seq<i32>, start: int, len1: int, len2: int)
    requires
        len1 >= 0,
        len2 >= 0,
        start >= 0,
        start + len1 + len2 <= a.len()
    ensures
        sum_range(a, start, len1 + len2) == sum_range(a, start, len1) + sum_range(a, start + len1, len2)
    decreases len1
{
    if len1 <= 0 {
        assert(sum_range(a, start, len1) == 0);
        assert(sum_range(a, start, len1 + len2) == sum_range(a, start, len2));
    } else {
        assert(sum_range(a, start, len1 + len2) == a[start] + sum_range(a, start + 1, len1 - 1 + len2));
        sum_range_split(a, start + 1, len1 - 1, len2);
        assert(sum_range(a, start + 1, len1 - 1 + len2) == sum_range(a, start + 1, len1 - 1) + sum_range(a, start + len1, len2));
        assert(sum_range(a, start, len1) == a[start] + sum_range(a, start + 1, len1 - 1));
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
    let mut i: usize = start;
    let mut sum: i32 = 0;
    
    while i < finish
        invariant
            start <= i <= finish,
            finish <= a.len(),
            sum == sum_range(a@, start as int, (i - start) as int)
    {
        proof {
            sum_range_split(a@, start as int, (i - start) as int, 1);
            sum_range_single(a@, i as int);
        }
        sum = sum + a[i];
        i = i + 1;
    }
    
    sum
}
// </vc-code>


}
fn main() {}