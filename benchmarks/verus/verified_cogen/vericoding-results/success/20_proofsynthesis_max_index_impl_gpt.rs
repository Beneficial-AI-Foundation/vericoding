// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn is_max_index(s: Seq<i32>, i: int) -> bool { 0 <= i && i < s.len() && forall|k: int| 0 <= k && k < s.len() ==> s[i] >= s[k] }

proof fn max_inv_extend(s: Seq<i32>, max_idx: int, i: int)
    requires
        1 <= s.len(),
        0 <= max_idx < i,
        i < s.len(),
        forall|k: int| 0 <= k < i ==> s[max_idx] >= s[k],
        s[i] <= s[max_idx]
    ensures
        forall|k: int| 0 <= k < i + 1 ==> s[max_idx] >= s[k]
{ }

proof fn max_choose_new(s: Seq<i32>, max_idx: int, i: int)
    requires
        1 <= s.len(),
        0 <= max_idx < i,
        i < s.len(),
        forall|k: int| 0 <= k < i ==> s[max_idx] >= s[k],
        s[i] > s[max_idx]
    ensures
        forall|k: int| 0 <= k < i + 1 ==> s[i] >= s[k]
{ }
// </vc-helpers>

// <vc-spec>
fn myfun1(x: &Vec<i32>) -> (max_index: usize)

    requires
        x.len() >= 1,

    ensures
        forall|k: int| 0 <= k < x.len() ==> x[max_index as int] >= x[k],
        max_index < x.len(),
// </vc-spec>
// <vc-code>
{
    let n = x.len();
    let mut max_index: usize = 0;
    let mut i: usize = 1;
    while i < n
        invariant
            n == x.len(),
            1 <= n,
            i <= n,
            max_index < i,
            max_index < n,
            forall|k: int| 0 <= k < i ==> x@[(max_index as int)] >= x@[k],
        decreases n - i
    {
        if x[i] > x[max_index] {
            proof {
                max_choose_new(x@, max_index as int, i as int);
            }
            max_index = i;
        } else {
            proof {
                max_inv_extend(x@, max_index as int, i as int);
            }
        }
        i = i + 1;
    }
    max_index
}
// </vc-code>

}
fn main() {}