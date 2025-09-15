// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn sum_to(a: &Vec<i32>, n: int) -> int
    decreases n
{
    if n <= 0 { 0 } else { sum_to(a, n - 1) + a[n - 1] }
}
// </vc-preamble>

// <vc-helpers>
proof fn sum_to_succ(a: &Vec<i32>, n: int)
    requires 0 <= n && n < a.len() as int
    ensures sum_to(a, n + 1) == sum_to(a, n) + a[n]
{
}

// </vc-helpers>

// <vc-spec>
fn array_sum(a: &Vec<i32>) -> (result: i32)
    requires a.len() > 0,
    ensures
        result == sum_to(a, a.len() as int),
// </vc-spec>
// <vc-code>
{
    let mut acc: i32 = 0;
    let mut i: int = 0;
    while i < a.len() as int
        invariant 0 <= i && i <= a.len() as int
        invariant acc as int == sum_to(a, i)
    {
        let ai: i32 = a[i as usize];
        acc = acc + ai;
        i = i + 1;
    }
    acc
}
// </vc-code>

}
fn main() {}