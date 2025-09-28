// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

proof fn sum_range_split(a: Seq<i32>, start: int, mid: int, end: int) 
    requires start >= 0, mid >= start, end >= mid, end <= a.len()
    ensures sum_range(a, start, end - start) == sum_range(a, start, mid - start) + sum_range(a, mid, end - mid)
    decreases end - mid
{
    if mid < end {
        let next = mid + 1;
        assert(sum_range(a, start, next - start) == sum_range(a, start, mid - start) + a[mid]) by {
            if next - start > 0 {
                sum_range_recursive(a, start, next - start);
            }
        };
        sum_range_split(a, start, next, end);
        assert(sum_range(a, start, end - start) == sum_range(a, start, mid - start) + a[mid] + sum_range(a, next, end - next));
        sum_range_recursive(a, mid, end - mid);
    }
}

proof fn sum_range_spec(a: Seq<i32>, start: int, len: int) 
    requires start >= 0, len >= 0, start + len <= a.len()
    ensures sum_range(a, start, len) == sum_range_recursive_calc(a, start, len)
    decreases len
{
    if len == 0 {
    } else {
        sum_range_spec(a, start + 1, len - 1);
    }
}

spec fn sum_range_recursive_calc(a: Seq<i32>, start: int, len: int) -> int
    decreases len
{
    if len <= 0 {
        0
    } else {
        a[start] + sum_range_recursive_calc(a, start + 1, len - 1)
    }
}

proof fn sum_range_empty(a: Seq<i32>, start: int, len: int) 
    ensures len <= 0 || start < 0 || start + len > a.len() ==> sum_range(a, start, len) == 0
{
}

proof fn sum_range_recursive(a: Seq<i32>, start: int, len: int) 
    requires start >= 0, len >= 0, start + len <= a.len(), len > 0
    ensures sum_range(a, start, len) == a[start] + sum_range(a, start + 1, len - 1)
{
}

/* helper modified by LLM (iteration 5): Fixed sequence indexing syntax to use @ operator */

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
    /* code modified by LLM (iteration 5): Fixed sequence indexing and verification */
    let mut result: i32 = 0;
    let mut i: usize = start;
    
    while i < finish
        invariant
            start <= i, i <= finish,
            result == sum_range_recursive_calc(a@, start as int, (i - start) as int)
        decreases finish - i
    {
        let current: usize = i;
        i = i + 1;
        proof {
            assert(current >= start && current < finish) by {
                assert(start <= current && current < finish);
            };
            assert(0 <= current as int && current as int < a@.len());
            sum_range_spec(a@, start as int, (current - start) as int);
            sum_range_spec(a@, start as int, (i - start) as int);
        };
        result = result + a[current];
    }
    
    proof {
        sum_range_spec(a@, start as int, (finish - start) as int);
    }
    
    result
}
// </vc-code>


}
fn main() {}