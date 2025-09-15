// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed compilation errors by making spec functions recursive and adding proper syntax */
spec fn max_in_range(a: &Vec<i32>, start: int, end: int) -> i32
    requires 0 <= start < end <= a.len()
    decreases end - start
{
    if start + 1 == end {
        a[start as usize]
    } else {
        let mid_max = max_in_range(a, start + 1, end);
        if a[start as usize] > mid_max { a[start as usize] } else { mid_max }
    }
}

spec fn exists_max_in_range(a: &Vec<i32>, start: int, end: int, val: i32) -> bool
    requires 0 <= start < end <= a.len()
{
    exists|i: int| start <= i < end && a[i as usize] == val
}

proof fn max_properties_lemma(a: &Vec<i32>, start: int, end: int)
    requires 0 <= start < end <= a.len()
    ensures forall|i: int| start <= i < end ==> a[i as usize] <= max_in_range(a, start, end)
    ensures exists_max_in_range(a, start, end, max_in_range(a, start, end))
{
    if start + 1 == end {
        assert(a[start as usize] == max_in_range(a, start, end));
    } else {
        max_properties_lemma(a, start + 1, end);
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
{
    /* code modified by LLM (iteration 5): fixed logic and added proper verification */
    let max_val = if x == 0 { a[0] } else {
        let mut max_so_far = a[0];
        let mut i = 1;
        while i < x
            invariant
                1 <= i <= x,
                forall|j: int| 0 <= j < i ==> a[j as usize] <= max_so_far,
                exists|j: int| 0 <= j < i && a[j as usize] == max_so_far
        {
            if a[i] > max_so_far {
                max_so_far = a[i];
            }
            i += 1;
        }
        max_so_far
    };
    
    let mut pos = x;
    while pos < a.len() - 1
        invariant
            x <= pos < a.len(),
            forall|i: int| 0 <= i < x ==> a[i as usize] <= max_val,
            exists|i: int| 0 <= i < x && a[i as usize] == max_val,
            forall|i: int| x <= i <= pos ==> a[i as usize] <= max_val
    {
        if a[pos] > max_val {
            break;
        }
        pos += 1;
    }
    
    (max_val, pos)
}
// </vc-code>

}
fn main() {}