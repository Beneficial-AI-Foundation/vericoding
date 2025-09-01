use vstd::prelude::*;

verus! {

// <vc-helpers>

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
   let len = l@.len();
   if len <= 1 {
       return true;
   }
   let mut i = 0;
   let mut is_increasing = true;
   let mut is_decreasing = true;
   while i < len - 1
       invariant 0 <= i <= len - 1
   {
       if l@[i] > l@[i + 1] {
           is_increasing = false;
       }
       if l@[i] < l@[i + 1] {
           is_decreasing = false;
       }
       i += 1;
   }
   if is_increasing || is_decreasing {
       return true;
   } else {
       return false;
   }
}
// </vc-code>

fn main() {}
}