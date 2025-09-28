use vstd::prelude::*;

verus! {

// <vc-helpers>
/// REQUIRES: Handshake proofs to support the implementation and verification of the CODE section.
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
fn canyon_search(a: &[i32], b: &[i32]) -> (d: u32)
  requires 
      a.len() != 0 && b.len() != 0,
      forall|i: int, j: int| 0 <= i < j < a.len() ==> a[i] <= a[j],
      forall|i: int, j: int| 0 <= i < j < b.len() ==> b[i] <= b[j],
  ensures
      exists|i: int, j: int| 0 <= i < a.len() && 0 <= j < b.len() && 
          d as int == (if a[i] < b[j] { 
              b[j] - a[i]
          } else { 
              a[i] - b[j]
          }),
      forall|i: int, j: int| 0 <= i < a.len() && 0 <= j < b.len() ==> 
          d as int <= (if a[i] < b[j] { 
              b[j] - a[i]
          } else { 
              a[i] - b[j]
          }),
// </vc-spec>
// <vc-code>
{
    let a_view = a.view();
    let b_view = b.view();
    let mut min_diff: u32 = (if a_view[0] < b_view[0] { b_view[0] - a_view[0] } else { a_view[0] - b_view[0] }) as u32;
    for i in 0..a_view.len() {
        for j in 0..b_view.len() {
            let current: u32 = (if a_view[i] < b_view[j] { b_view[j] - a_view[i] } else { a_view[i] - b_view[j] }) as u32;
            if current < min_diff {
                min_diff = current;
            }
        }
    }
    min_diff
}
// </vc-code>
// </vc-code>

fn main() {}

}