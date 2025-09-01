use vstd::prelude::*;

verus! {

// <vc-helpers>
fn lemma_transitive_less(l: Seq<i32>, len_it: int, len: int)
#[verifier::spoof]
ensures forall |p: int, q: int| 0 <= p < q < len ==> l.index(p) <= l.index(q)
requires 0 <= len_it < len, len == l.len(), forall |k: int| #![trigger l.index(k)] #![trigger l.index(k+1)] 0 <= k < len_it ==> l.index(k) <= l.index(k+1) {
}

fn lemma_transitive_greater(l: Seq<i32>, len_it: int, len: int)
#[verifier::spoof]
ensures forall |p: int, q: int| 0 <= p < q < len ==> l.index(p) >= l.index(q)
requires 0 <= len_it < len, len == l.len(), forall |k: int| #![trigger l.index(k)] #![trigger l.index(k+1)] 0 <= k < len_it ==> l.index(k) >= l.index(k+1) {
}
// </vc-helpers>

// <vc-spec>
fn monotonic(l: Vec<i32>) -> (ret: bool)
    // post-conditions-start
    ensures
        ret <==> (forall|i: int, j: int| 0 <= i < j < l@.len() ==> l@.index(i) <= l@.index(j)) || (
        forall|i: int, j: int| 0 <= i < j < l@.len() ==> l@.index(i) >= l@.index(j)),
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
   let len: int = l@.len() as int;
   if len <= 1 {
       return true;
   }
   let mut i: int = 0;
   let mut is_increasing = true;
   let mut is_decreasing = true;
   while i < len - 1
       invariant 0 <= i <= len - 1,
       invariant len >= 2
       invariant if is_increasing { forall |k: int| #![trigger l@.index(k)] #![trigger l@.index(k+1)] 0 <= k < i ==> l@.index(k) <= l@.index(k+1) },
       invariant if is_decreasing { forall |k: int| #![trigger l@.index(k)] #![trigger l@.index(k+1)] 0 <= k < i ==> l@.index(k) >= l@.index(k+1) },
       invariant i + 1 <= len
   {
       if l@.index(i) > l@.index(i + 1) {
           is_increasing = false;
       }
       if l@.index(i) < l@.index(i + 1) {
           is_decreasing = false;
       }
       i += 1;
   }
   let ret = is_increasing || is_decreasing;
   if ret {
       proof {
           if is_increasing {
               lemma_transitive_less(l@, len - 1, len);
           }
           if is_decreasing {
               lemma_transitive_greater(l@, len - 1, len);
           }
       }
   }
   ret
}
// </vc-code>

fn main() {}
}