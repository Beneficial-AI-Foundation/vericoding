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
    let mut i: i32 = 0;
    while i < a.len()
        invariant
            0 <= i,
            i <= a.len(),
            forall|k: int| 0 <= k && k < i as int ==> #[trigger] a[k] != key
    {
        if a[i as int] == key {
            return i;
        } else {
            assert(a[i as int] != key);
            let old_i = i;
            i = i + 1;
            assert forall|k: int| 0 <= k && k < i as int implies #[trigger] a[k] != key by {
                if 0 <= k && k < i as int {
                    if k < old_i as int {
                        assert(0 <= k && k < old_i as int);
                    } else {
                        assert(i as int == old_i as int + 1);
                        assert(k >= old_i as int);
                        assert(k < old_i as int + 1);
                        assert(k == old_i as int);
                        assert(a[old_i as int] != key);
                        assert(a[k] != key);
                    }
                }
            };
        }
    }
    assert(i == a.len());
    assert forall|k: int| 0 <= k && k < a.len() implies #[trigger] a[k] != key by {
        if 0 <= k && k < a.len() {
            assert(i == a.len());
            assert(0 <= k && k < i as int);
        }
    };
    -1
}
// </vc-code>

fn main() {}

}