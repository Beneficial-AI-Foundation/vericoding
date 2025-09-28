// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn number_to_name(n: int) -> &'static str {
  if n == 1 { "One" }
  else if n == 2 { "Two" }
  else if n == 3 { "Three" }
  else if n == 4 { "Four" }
  else if n == 5 { "Five" }
  else if n == 6 { "Six" }
  else if n == 7 { "Seven" }
  else if n == 8 { "Eight" }
  else if n == 9 { "Nine" }
  else { "Unknown" }
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn sort_seq(s: Vec<i8>) -> (sorted: Vec<i8>)
  ensures 
    forall|i: int, j: int| 0 <= i < j < sorted.len() ==> sorted[i] as int <= sorted[j] as int &&
    sorted.len() == s.len() &&
    s@.to_multiset() == sorted@.to_multiset()
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed syntax error - use && instead of ==> between conditions */
    let mut sorted = s.clone();
    let n = sorted.len();
    
    if n == 0 {
        return sorted;
    }
    
    let mut i: usize = 0;
    while i < n
        invariant
            sorted.len() == s.len(),
            sorted.len() == n,
            s@.to_multiset() == sorted@.to_multiset(),
            forall|k: int, l: int| 0 <= k < l <= i as int && l < sorted.len() ==> sorted[k] as int <= sorted[l] as int,
            forall|k: int| 0 <= k < i as int && i as int < sorted.len() ==> sorted[k] as int <= sorted[i] as int,
            i <= n
    {
        let mut j: usize = i + 1;
        let mut min_idx: usize = i;
        
        while j < n
            invariant
                sorted.len() == n,
                i < n,
                i + 1 <= j,
                j <= n,
                min_idx < n,
                i <= min_idx,
                min_idx < j,
                s@.to_multiset() == sorted@.to_multiset(),
                forall|k: int| i as int <= k && k < j as int ==> sorted[min_idx as int] as int <= sorted[k] as int
        {
            if sorted[j] < sorted[min_idx] {
                min_idx = j;
            }
            j = j + 1;
        }
        
        if min_idx != i {
            let temp = sorted[i];
            sorted.set(i, sorted[min_idx]);
            sorted.set(min_idx, temp);
        }
        
        i = i + 1;
    }
    
    sorted
}
// </vc-code>


}

fn main() {}