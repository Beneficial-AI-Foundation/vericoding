// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): comparator for stable ordering */
spec fn less_index(a: Vec<i32>, i: usize, j: usize) -> bool { a[i] < a[j] || (a[i] == a[j] && i < j) }
// </vc-helpers>

// <vc-spec>
fn argsort(a: Vec<i32>) -> (result: Vec<usize>)
    ensures 
        result.len() == a.len(),

        forall|i: int| 0 <= i < result.len() ==> #[trigger] result[i] < a.len(),

        forall|i: int, j: int| 0 <= i < j < result.len() ==> 
            a[#[trigger] result[i] as int] <= a[#[trigger] result[j] as int],

        forall|i: int, j: int| 0 <= i < j < result.len() && 
            a[#[trigger] result[i] as int] == a[#[trigger] result[j] as int] ==> 
            result[i] < result[j]
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): stable insertion building a sorted index vector */
    let n: int = a.len() as int;
    let mut sorted: Vec<usize> = Vec::new();
    let mut p: int = 0;
    while p < n
        invariant 0 <= p && p <= n,
        invariant sorted.len() as int == p,
        invariant forall |x: int, y: int| 0 <= x < y < p ==> less_index(a, sorted[x as usize], sorted[y as usize]),
        decreases n - p
    {
        let cur: usize = p as usize;
        let mut pos: int = 0;
        while pos < p && !(less_index(a, cur, sorted[pos as usize]))
            invariant 0 <= pos && pos <= p,
            invariant forall |x: int, y: int| 0 <= x < y < p ==> less_index(a, sorted[x as usize], sorted[y as usize]),
            decreases p - pos
        {
            pos += 1;
        }
        let mut new_sorted: Vec<usize> = Vec::new();
        let mut q: int = 0;
        while q < pos
            invariant 0 <= q && q <= pos,
            decreases pos - q
        {
            new_sorted.push(sorted[q as usize]);
            q += 1;
        }
        new_sorted.push(cur);
        q = pos;
        while q < p
            invariant 0 <= q && q <= p,
            decreases p - q
        {
            new_sorted.push(sorted[q as usize]);
            q += 1;
        }
        proof {
            assert(new_sorted.len() as int == p + 1);
            assert(forall |x: int, y: int| 0 <= x < y < new_sorted.len() as int ==> less_index(a, new_sorted[x as usize], new_sorted[y as usize]));
        }
        sorted = new_sorted;
        p += 1;
    }
    sorted
}
// </vc-code>

}
fn main() {}