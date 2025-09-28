// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): No changes required; helper functions are correct. */
proof fn sub_inequality_lemma(m: int, n: int, x: int, y: int)
    requires
        x <= m,
        y >= n,
    ensures
        x - y <= m - n,
{
}

fn find_max(a: &[i32]) -> (max_val: i32)
    requires
        a.len() > 0,
    ensures
        exists|k: int| 0 <= k < a.len() && a[k] == max_val,
        forall|k: int| 0 <= k < a.len() ==> a[k] <= max_val,
{
    let mut max_val = a[0];
    let mut i: usize = 1;
    while i < a.len()
        invariant
            1 <= i <= a.len(),
            exists|k: int| 0 <= k < i as int && a[k] == max_val,
            forall|k: int| 0 <= k < i as int ==> a[k] <= max_val,
        decreases a.len() - i
    {
        if a[i] > max_val {
            max_val = a[i];
        }
        i = i + 1;
    }
    max_val
}

fn find_min(a: &[i32]) -> (min_val: i32)
    requires
        a.len() > 0,
    ensures
        exists|k: int| 0 <= k < a.len() && a[k] == min_val,
        forall|k: int| 0 <= k < a.len() ==> a[k] >= min_val,
{
    let mut min_val = a[0];
    let mut i: usize = 1;
    while i < a.len()
        invariant
            1 <= i <= a.len(),
            exists|k: int| 0 <= k < i as int && a[k] == min_val,
            forall|k: int| 0 <= k < i as int ==> a[k] >= min_val,
        decreases a.len() - i
    {
        if a[i] < min_val {
            min_val = a[i];
        }
        i = i + 1;
    }
    min_val
}
// </vc-helpers>

// <vc-spec>
fn max_difference(a: &[i32]) -> (diff: i32)
    requires a.len() > 1
    ensures forall|i: int, j: int| 0 <= i < a.len() && 0 <= j < a.len() ==> a[i] - a[j] <= diff
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): Fixed illegal requires/ensures syntax in forall proof. */
    let max_val = find_max(a);
    let min_val = find_min(a);

    proof {
        forall|i: int, j: int|
            0 <= i < a.len() && 0 <= j < a.len()
        {
            sub_inequality_lemma(max_val as int, min_val as int, a[i] as int, a[j] as int);
        }
    }

    max_val - min_val
}
// </vc-code>

}
fn main() {}