// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): removed requires/ensures from spec function */
spec fn max_in_range(a: &Vec<i32>, start: int, end: int) -> i32
    decreases end - start,
{
    if start == end - 1 {
        a[start]
    } else {
        let mid_max = max_in_range(a, start + 1, end);
        if a[start] > mid_max { a[start] } else { mid_max }
    }
}

proof fn lemma_max_exists(a: &Vec<i32>, start: int, end: int, max_val: i32)
    requires
        a.len() > 0,
        0 <= start < end,
        end <= a.len(),
        max_val == max_in_range(a, start, end),
    ensures
        exists|i: int| start <= i < end && a[i] == max_val,
        forall|i: int| start <= i < end ==> a[i] <= max_val,
{}
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
/* code modified by LLM (iteration 5): added decreases clauses to both while loops */
{
    let mut current_max = a[0];
    let mut p = x;
    
    // Find the max in range [0, x)
    let mut i = 1;
    while i < x
        invariant
            1 <= i <= x,
            forall|j: int| 0 <= j < i ==> a[j] <= current_max,
            exists|j: int| 0 <= j < i && a[j] == current_max,
        decreases x - i
    {
        if a[i] > current_max {
            current_max = a[i];
        }
        i = i + 1;
    }
    
    // Now find the first position where we exceed current_max
    while p < a.len() - 1
        invariant
            x <= p < a.len(),
            forall|j: int| 0 <= j < x ==> a[j] <= current_max,
            exists|j: int| 0 <= j < x && a[j] == current_max,
            forall|j: int| x <= j <= p ==> a[j] <= current_max,
        decreases a.len() - 1 - p
    {
        if a[p + 1] > current_max {
            break;
        }
        p = p + 1;
    }
    
    (current_max, p)
}
// </vc-code>

}
fn main() {}