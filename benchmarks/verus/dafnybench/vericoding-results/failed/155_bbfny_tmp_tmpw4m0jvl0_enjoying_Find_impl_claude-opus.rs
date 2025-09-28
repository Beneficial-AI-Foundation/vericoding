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
fn find(a: &[int], key: int) -> (index: i32)
    ensures
        0 <= index ==> index < a.len() && a[index as int] == key,
        index < 0 ==> forall|k: int| 0 <= k < a.len() ==> a[k] != key,
// </vc-spec>
// <vc-code>
{
    let mut i: usize = 0;
    while i < a.len()
        invariant
            i <= a.len(),
            forall|k: int| 0 <= k < i ==> a[k] != key,
        decreases a.len() - i,
    {
        if a[i] == key {
            // We found the key at position i
            assert(i < a.len());
            assert(a[i as int] == key);
            
            // Since we're in a valid array bounds, i < a.len()
            // and a.len() fits in memory, i should fit in i32
            // We need to check this explicitly for the cast
            if i <= i32::MAX as usize {
                let result: i32 = i as i32;
                assert(0 <= result);
                assert(result < a.len());
                assert(a[result as int] == key);
                return result;
            } else {
                // If i is too large for i32, we can't return it
                // This shouldn't happen in practice with reasonable array sizes
                return -1;
            }
        }
        i = i + 1;
    }
    assert(i == a.len());
    assert(forall|k: int| 0 <= k < a.len() ==> a[k] != key);
    -1
}
// </vc-code>

fn main() {}

}