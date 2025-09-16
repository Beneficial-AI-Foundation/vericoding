// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
fn max_i32(a: i32, b: i32) -> i32 { if a >= b { a } else { b } }
// </vc-helpers>

// <vc-spec>
fn max_element(a: &Vec<i32>) -> (max: i32)

    requires
        a.len() > 0,

    ensures
        forall|i: int| 0 <= i < a.len() ==> a[i] <= max,
        exists|i: int| 0 <= i < a.len() && a[i] == max,
// </vc-spec>
// <vc-code>
{
    let mut i: usize = 1;
    let mut m: i32 = a[0];
    while i < a.len()
        invariant
            1 <= i as int <= a.len() as int,
            forall|j: int| 0 <= j < i as int ==> a[j] <= m,
            exists|j: int| 0 <= j < i as int && a[j] == m,
        decreases a.len() - i
    {
        let v = a[i];
        if v > m {
            m = v;
        }
        i = i + 1;
    }
    m
}
// </vc-code>

}
fn main() {}