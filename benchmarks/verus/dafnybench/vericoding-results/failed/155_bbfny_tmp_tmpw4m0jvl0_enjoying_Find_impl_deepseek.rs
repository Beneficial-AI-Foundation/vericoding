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
proof fn lemma_sorted_contains(a: &[int], key: int, low: int, high: int)
    requires
        sorted(a),
        0 <= low <= high <= a.len(),
    ensures
        forall|k: int| low <= k < high ==> a[k] != key ==> (key < a[k] || (exists|l: int| k < l < high && key > a[l])),
    decreases high - low
{
    if low < high {
        let mid = low + (high - low) / 2;
        lemma_sorted_contains(a, key, low, mid);
        lemma_sorted_contains(a, key, mid, high);
    }
}

proof fn lemma_sorted_binary_search(a: &[int], key: int, low: int, high: int)
    requires
        sorted(a),
        0 <= low <= high <= a.len(),
    ensures
        forall|k: int| 0 <= k < a.len() ==> a[k] == key ==> low <= k < high,
    decreases high - low
{
    if low < high {
        let mid = low + (high - low) / 2;
        if key <= a[mid] {
            lemma_sorted_binary_search(a, key, low, mid + 1);
        } else {
            lemma_sorted_binary_search(a, key, mid + 1, high);
        }
    }
}

proof fn lemma_sorted_implies_monotonic(a: &[int], i: int, j: int)
    requires
        sorted(a),
        0 <= i <= j < a.len(),
    ensures
        a[i] <= a[j],
{
}
// </vc-helpers>

// <vc-spec>
fn find(a: &[int], key: int) -> (index: i32)
    ensures
        0 <= index ==> index < a.len() && a[index as int] == key,
        index < 0 ==> forall|k: int| 0 <= k < a.len() ==> a[k] != key,
// </vc-spec>
// <vc-code>
{
    let mut low: i32 = 0;
    let mut high: i32 = a.len() as i32;
    while low < high
        invariant
            0 <= low <= high <= a.len() as i32,
            forall|k: int| 0 <= k < a.len() && a[k] == key ==> low <= (k as i32) < high,
        decreases (high - low) as nat
    {
        let mid = low + (high - low) / 2;
        if a[mid as int] == key {
            return mid;
        } else if a[mid as int] < key {
            proof {
                lemma_sorted_binary_search(a, key, low as int, high as int);
                lemma_sorted_implies_monotonic(a, mid as int, (high - 1) as int);
            }
            low = mid + 1;
        } else {
            proof {
                lemma_sorted_binary_search(a, key, low as int, high as int);
                lemma_sorted_implies_monotonic(a, low as int, mid as int);
            }
            high = mid;
        }
    }
    -1
}
// </vc-code>

fn main() {}

}