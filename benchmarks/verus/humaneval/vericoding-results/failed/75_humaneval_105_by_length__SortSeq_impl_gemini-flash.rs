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
/* helper modified by LLM (iteration 5): removed explicit proof block, relying on `requires` clause for `usize` cast safety */
fn swap<T>(v: &mut Vec<T>, i: int, j: int)
    requires
        0 <= i < v.len(),
        0 <= j < v.len(),
    ensures
        v.len() == old(v).len(),
        v[i] == old(v)[j],
        v[j] == old(v)[i],
        forall|k: int| 0 <= k < v.len() && k != i && k != j ==> v[k] == old(v)[k],
{
    v.swap(i as usize, j as usize);
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
/* code modified by LLM (iteration 5): Fixed compilation error with array indexing, ensuring proper Verus syntax. */
{
    let mut arr = s;
    let n = arr.len();

    if n <= 1 {
        return arr;
    }

    let mut i: int = 0;
    while i < n
        invariant
            0 <= i <= n,
            arr.len() == n,
            s@.to_multiset() == arr@.to_multiset(),
        decreases n - i
    {
        let mut min_idx: int = i;
        let mut j: int = i + 1;
        while j < n
            invariant
                i <= min_idx < n,
                i + 1 <= j <= n,
                arr.len() == n,
                forall|k: int| i <= k < j ==> arr@[min_idx as int] as int <= arr@[k as int] as int,
                s@.to_multiset() == arr@.to_multiset(),
            decreases n - j
        {
            if arr@[j as int] as int < arr@[min_idx as int] as int {
                min_idx = j;
            }
            j = j + 1;
        }

        if min_idx != i {
            swap(&mut arr, i, min_idx);
        }

        i = i + 1;
    }
    arr
}
// </vc-code>


}

fn main() {}