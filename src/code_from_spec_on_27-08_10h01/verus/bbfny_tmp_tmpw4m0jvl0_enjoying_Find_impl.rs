use vstd::prelude::*;

verus! {

// shenanigans going through the dafny tutorial




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

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
// <vc-spec>
fn find(a: &[int], key: int) -> (index: i32)
    ensures
        0 <= index ==> index < a.len() && a[index as int] == key,
        index < 0 ==> forall|k: int| 0 <= k < a.len() ==> a[k] != key,
// </vc-spec>
// </vc-spec>

// <vc-code>
{
    let mut i = 0;
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            forall|k: int| 0 <= k < i ==> a[k] != key,
        decreases a.len() - i
    {
        if a[i] == key {
            assert(i < a.len());
            assert(a[i as int] == key);
            assert(0 <= i);
            assert(i < i32::MAX);
            return (i as i32);
        }
        i += 1;
    }
    assert(i == a.len());
    assert(forall|k: int| 0 <= k < a.len() ==> a[k] != key);
    -1
}
// </vc-code>

fn main() {}

}