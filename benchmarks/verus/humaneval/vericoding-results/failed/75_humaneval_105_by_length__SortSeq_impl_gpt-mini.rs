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
/* helper modified by LLM (iteration 5): convert usize to int for specs */
spec fn usize_to_int(u: usize) -> int { u as int }
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
    /* code modified by LLM (iteration 5): insertion sort using slice correctly */
    let mut dest: Vec<i8> = Vec::new();
    let mut i: usize = 0;
    while i < s.len()
        invariant
            dest.len() == i,
            dest@.to_multiset() == s@.slice(0, i as int).to_multiset(),
            forall|p: int, q: int| 0 <= p < q && q < dest.len() as int ==> dest@[p] <= dest@[q],
        decreases s.len() - i
    {
        let x: i8 = s[i];
        dest.push(x);
        let mut k: usize = dest.len() - 1;
        while k > 0 && dest[k - 1] > dest[k]
            invariant
                0 <= (k as int) && (k as int) <= dest.len() as int,
                dest@.to_multiset() == s@.slice(0, ((i as int) + 1)).to_multiset(),
                forall|p: int, q: int| 0 <= p < q && q < (k as int) ==> dest@[p] <= dest@[q],
            decreases k
        {
            dest.swap(k - 1, k);
            k = k - 1;
        }
        i = i + 1;
    }
    dest
}
// </vc-code>


}

fn main() {}