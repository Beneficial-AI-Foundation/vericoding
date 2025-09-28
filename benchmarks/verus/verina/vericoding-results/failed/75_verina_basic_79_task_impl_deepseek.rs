// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed compilation error by adding result variable declaration */
proof fn find_max_in_range(a: Seq<i32>, start: int, end: int) -> (result: (i32, int))
    requires
        start <= end,
        end <= a.len(),
        start >= 0,
    ensures
        start <= result.1 < end,
        forall|i: int| start <= i < end ==> a[i] <= result.0,
        a[result.1] == result.0
{
    if start + 1 == end {
        (a[start], start)
    } else {
        let mid = (start + end) / 2;
        let (left_max, left_idx) = find_max_in_range(a, start, mid);
        let (right_max, right_idx) = find_max_in_range(a, mid, end);
        if left_max >= right_max {
            (left_max, left_idx)
        } else {
            (right_max, right_idx)
        }
    }
}
// </vc-helpers>

// <vc-spec>
fn online_max(a: &Vec<i32>, x: usize) -> (result: (i32, usize))
    requires
        a.len() > 0,
        x < a.len(),
    ensures
        ({
            let (m, p) = result;
            x <= p && p < a.len()
            && (forall|i: int| 0 <= i < x ==> a[i] <= m)
            && (exists|i: int| 0 <= i < x && a[i] == m)
            && ((p < a.len() - 1) ==> (exists|i: int| x <= i <= p && a[i] > m))
            && ((forall|i: int| x <= i < a.len() ==> a[i] <= m) ==> p == a.len() - 1)
        })
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Fixed compilation error by declaring result variable */
{
    let mut current_max = a[x];
    let mut current_pos = x;
    let mut i = x + 1;
    
    while i < a.len()
        invariant
            x <= current_pos < a.len(),
            forall|j: int| 0 <= j < i ==> a[j] <= current_max,
            exists|j: int| 0 <= j < i && a[j] == current_max,
            i <= a.len()
        decreases a.len() - i
    {
        if a[i] > current_max {
            current_max = a[i];
            current_pos = i;
        }
        i += 1;
    }
    
    let result = (current_max, current_pos);
    result
}
// </vc-code>

}
fn main() {}