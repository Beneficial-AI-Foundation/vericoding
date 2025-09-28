// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
proof fn trivial_helper()
    ensures
        true,
{
}
// </vc-helpers>

// <vc-spec>
fn cum_sum(a: Vec<i8>) -> (result: Vec<i8>)
    requires a.len() > 0,
    ensures 
        result.len() == a.len(),
        result[0] == a[0],
        forall|i: int| 1 <= i < a.len() ==> result[i as int] as int == result[(i - 1) as int] as int + a[i as int] as int
// </vc-spec>
// <vc-code>
{
    let n = a.len();
    let mut result: Vec<i8> = Vec::new();
    result.push(a[0]);
    let mut i: usize = 1;
    while i < n
        invariant
            1 <= i as int <= n as int,
            result.len() == i,
            result[0] == a[0],
            forall|j: int| 1 <= j < i as int ==> result[j as int] as int == result[(j - 1) as int] as int + a[j as int] as int,
        decreases n - i
    {
        let prev = result[i - 1];
        let next = prev + a[i];
        result.push(next);
        i = i + 1;
    }
    result
}
// </vc-code>


}
fn main() {}