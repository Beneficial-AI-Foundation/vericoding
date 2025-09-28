use vstd::prelude::*;

verus! {

// Insertion sort.
//
// Author: Snorri Agnarsson, snorri@hi.is


spec fn is_sorted(s: Seq<int>) -> bool {
    forall|p: int, q: int| 0 <= p < q < s.len() ==> s[p] <= s[q]
}

// <vc-helpers>
spec fn insert_into_sorted(sorted: Seq<int>, elem: int) -> (r: Seq<int>)
  requires is_sorted(sorted)
  ensures
      is_sorted(r),
      r.to_multiset() == sorted.to_multiset().insert(elem)
{
  if sorted.len() == 0 {
     Seq::singleton(elem)
  } else if sorted[0] > elem {
    Seq::singleton(elem).add(sorted)
  } else {
    Seq::singleton(sorted[0]).add(insert_into_sorted(sorted.subrange(1, sorted.len()), elem))
  }
}
// </vc-helpers>

// <vc-spec>
fn insertion_sort(s: Seq<int>) -> (r: Seq<int>)
    ensures
        s.to_multiset() == r.to_multiset(),
        is_sorted(r),
// </vc-spec>
// <vc-code>
{
  decreases(s.len());
  if s.len() == 0 {
     Seq::empty()
  } else {
    let sorted_tail = insertion_sort(s.subrange(1, s.len()));
    insert_into_sorted(sorted_tail, s[0])
  }
}
// </vc-code>

fn main() {}

}