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

proof fn lemma_seq_count_eq(s1: Seq<i8>, s2: Seq<i8>)
    ensures
        s1.to_multiset() == s2.to_multiset() <==> forall|v: i8| s1.count(v) == s2.count(v),
{
}

proof fn lemma_sorted_sequence_property(sorted: Seq<i8>)
    ensures
        forall|i: int, j: int| 0 <= i < j < sorted.len() ==> sorted[i] <= sorted[j],
{
}

proof fn lemma_sequence_length_preserved<T>(s1: Seq<T>, s2: Seq<T>)
    ensures
        s1.len() == s2.len() <==> s1.to_multiset().len() == s2.to_multiset().len(),
{
}

/* helper modified by LLM (iteration 5): fixed seq indexing syntax */
fn get_seq_elem(seq: Seq<i8>, index: int) -> i8
    requires
        0 <= index < seq.len(),
{
    seq[index]
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
    /* code modified by LLM (iteration 5): fixed type casting and indexing with proper int/uint conversions */
    let mut sorted = s.clone();
    let mut i: int = 0;
    
    while i < sorted.len() as int
        invariant
            sorted@.to_multiset() == s@.to_multiset(),
            sorted.len() == s.len(),
            0 <= i <= sorted.len() as int,
        decreases sorted.len() as int - i,
    {
        let mut j: int = i + 1;
        
        while j < sorted.len() as int
            invariant
                sorted@.to_multiset() == s@.to_multiset(),
                sorted.len() == s.len(),
                i < j <= sorted.len() as int,
                forall|k: int| 0 <= k < i ==> sorted[k as usize] <= sorted[i as usize],
            decreases sorted.len() as int - j,
        {
            if sorted[j as usize] < sorted[i as usize] {
                let temp = sorted[i as usize];
                sorted[i as usize] = sorted[j as usize];
                sorted[j as usize] = temp;
            }
            j += 1;
        }
        i += 1;
    }
    
    sorted
}
// </vc-code>


}

fn main() {}