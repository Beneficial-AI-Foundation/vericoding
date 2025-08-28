use vstd::prelude::*;

verus! {

// <vc-helpers>
proof fn lemma_max_in_range(a: Seq<i32>, x: usize, max_val: i32, max_idx: usize)
    requires
        1 <= x < a.len(),
        0 <= max_idx < x,
        a[max_idx] == max_val,
        forall|i: int| 0 <= i < x ==> #[trigger] a[i] <= max_val,
    ensures
        exists|i: int| 0 <= i < x && #[trigger] a[i] == max_val,
{
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
fn online_max(a: &[i32], x: usize) -> (result: (Ghost<i32>, usize))
    requires 
        1 <= x < a.len(),
        a.len() != 0,
    ensures
        x <= result.1 < a.len(),
        forall|i: int| 0 <= i < x ==> #[trigger] a[i] <= result.0@,
        exists|i: int| 0 <= i < x && #[trigger] a[i] == result.0@,
        x <= result.1 < a.len() - 1 ==> (forall|i: int| 0 <= i < result.1 ==> #[trigger] a[i] < a[result.1 as int]),
        (forall|i: int| x <= i < a.len() && #[trigger] a[i] <= result.0@) ==> result.1 == a.len() - 1
// </vc-spec>
// </vc-spec>

// <vc-code>
fn online_max(a: &[i32], x: usize) -> (result: (Ghost<i32>, usize))
    requires 
        1 <= x < a.len(),
        a.len() != 0,
    ensures
        x <= result.1 < a.len(),
        forall|i: int| 0 <= i < x ==> #[trigger] a[i] <= result.0@,
        exists|i: int| 0 <= i < x && #[trigger] a[i] == result.0@,
        x <= result.1 < a.len() - 1 ==> (forall|i: int| 0 <= i < result.1 ==> #[trigger] a[i] < a[result.1 as int]),
        (forall|i: int| x <= i < a.len() && #[trigger] a[i] <= result.0@) ==> result.1 == a.len() - 1
{
    let mut max_val = a[0];
    let mut max_idx = 0;

    let mut i = 1;
    while i < x
        invariant
            0 <= max_idx < i <= x,
            forall|j: int| 0 <= j < i ==> #[trigger] a[j] <= max_val,
            a[max_idx] == max_val,
    {
        if a[i] > max_val {
            max_val = a[i];
            max_idx = i;
        }
        i = i + 1;
    }

    proof {
        lemma_max_in_range(a@, x, max_val, max_idx);
    }

    let mut j = x;
    while j < a.len()
        invariant
            x <= j <= a.len(),
            forall|k: int| 0 <= k < x ==> #[trigger] a[k] <= max_val,
            a[max_idx] == max_val,
            0 <= max_idx < x,
            forall|k: int| x <= k < j ==> #[trigger] a[k] <= max_val,
    {
        if a[j] > max_val {
            return (Ghost(max_val), j);
        }
        j = j + 1;
    }

    (Ghost(max_val), a.len() - 1)
}
// </vc-code>

fn main() {
}

}