// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
fn find_min_index(s: Seq<i32>, start: int, end: int) -> (idx: int)
  requires
    0 <= start < end <= s.len(),
    
  ensures
    start <= idx < end,
    forall |k: int| start <= k < end ==> s[idx] <= s[k],
    
  decreases (end - start)
{
    let mut min_idx = start;
    let mut j = start + 1;
    while j < end
        invariant
            start <= min_idx < j <= end,
            forall |k: int| start <= k < j ==> s[min_idx] <= s[k],
            
        decreases (end - j)
    {
        if s[j] < s[min_idx] {
            min_idx = j;
        }
        j += 1;
    }
    min_idx
}
// </vc-helpers>

// <vc-spec>
fn selection_sort(a: &Vec<i32>) -> (result: Vec<i32>)
    ensures
        result.len() == a.len(),
        forall|i: int, j: int| 0 <= i <= j < result.len() ==> result[i] <= result[j],
        result@ =~= a@,
// </vc-spec>
// <vc-code>
{
    proof {
        let mut j = 0;
        let mut sorted: Seq<i32> = Seq::empty();
        let mut current: Seq<i32> = a@;
        while j < a.len()
            invariant
                j <= (a.len() as int),
                sorted.len() == j,
                current.len() == a.len() - j,
                forall |p: int, q: int| 0 <= p <= q < j ==> sorted[p] <= sorted[q],
                
            decreases ((a.len() as int) - j)
        {
            let min_idx = find_min_index(current, 0, current.len());
            let min_value = current[min_idx];
            sorted = sorted.push(min_value);
            current = current.take(min_idx).append(current.drop(min_idx + 1));
            j += 1;
        }
        Vec::new(sorted)
    }
}
// </vc-code>

}
fn main() {}