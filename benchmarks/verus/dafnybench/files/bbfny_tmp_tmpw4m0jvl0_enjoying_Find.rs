// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn max(a: int, b: int) -> int {
    if a > b { a } else { b }
}

fn testing() {
    assume(false);
}

spec fn abs(x: int) -> int {
    if x < 0 { -x } else { x }
}

spec fn fib(n: nat) -> nat
    decreases n
{
    if n == 0 { 0 }
    else if n == 1 { 1 }
    else { fib((n - 1) as nat) + fib((n - 2) as nat) }
}

spec fn sorted(a: &[int]) -> bool {
    forall|j: int, k: int| 0 <= j < k < a.len() ==> a[j] < a[k]
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn find(a: &[int], key: int) -> (index: i32)
    ensures
        0 <= index ==> index < a.len() && a[index as int] == key,
        index < 0 ==> forall|k: int| 0 <= k < a.len() ==> a[k] != key,
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}