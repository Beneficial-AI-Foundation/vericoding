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
/* helper modified by LLM (iteration 5): fixed lemma syntax by removing lemma keyword */
fn multiset_swap_preserves<T>(v1: Vec<T>, v2: Vec<T>, i: usize, j: usize)
    requires
        i < v1.len(),
        j < v1.len(),
        v2.len() == v1.len(),
        v2[i as int] == v1[j as int],
        v2[j as int] == v1[i as int],
        forall|k: int| 0 <= k < v1.len() && k != i && k != j ==> v2[k] == v1[k],
    ensures
        v1@.to_multiset() == v2@.to_multiset(),
{
    // This function helps prove multiset preservation during swaps
}
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
    /* code modified by LLM (iteration 5): simplified implementation without proof block */
    let mut sorted = s;
    let mut i = 0;
    
    while i < sorted.len()
        invariant
            i <= sorted.len(),
            sorted.len() == s.len(),
            s@.to_multiset() == sorted@.to_multiset(),
            forall|j: int, k: int| 0 <= j < k < i ==> sorted[j] as int <= sorted[k] as int,
        decreases sorted.len() - i
    {
        let mut min_idx = i;
        let mut j = i + 1;
        
        while j < sorted.len()
            invariant
                i < sorted.len(),
                i <= min_idx < sorted.len(),
                i + 1 <= j <= sorted.len(),
                sorted.len() == s.len(),
                s@.to_multiset() == sorted@.to_multiset(),
                forall|k: int, l: int| 0 <= k < l < i ==> sorted[k] as int <= sorted[l] as int,
                forall|k: int| i <= k < j ==> sorted[min_idx as int] as int <= sorted[k] as int,
            decreases sorted.len() - j
        {
            if sorted[j] < sorted[min_idx] {
                min_idx = j;
            }
            j += 1;
        }
        
        if min_idx != i {
            let temp = sorted[i];
            sorted.set(i, sorted[min_idx]);
            sorted.set(min_idx, temp);
        }
        
        i += 1;
    }
    
    sorted
}
// </vc-code>


}

fn main() {}