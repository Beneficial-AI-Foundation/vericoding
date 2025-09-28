use vstd::prelude::*;

verus! {

// <vc-helpers>
spec fn abs_diff_spec(a: int, b: int) -> int {
    if a < b {
        b - a
    } else {
        a - b
    }
}

fn abs_diff_exec(a: i32, b: i32) -> i32 {
    if a < b {
        b - a
    } else {
        a - b
    }
}
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
    let mut min_diff: i32 = abs_diff_exec(a[0], b[0]);
    let mut i: usize = 0;
    let mut j: usize = 0;

    while i < a.len() && j < b.len()
        invariant
            0 <= i && i <= a.len(),
            0 <= j && j <= b.len(),
            min_diff as int >= 0,
            forall|x: int, y: int| 
                #[trigger] abs_diff_spec(a[x] as int, b[y] as int)
                && 0 <= x < i as int && 0 <= y < b.len() as int 
                ==> min_diff as int <= abs_diff_spec(a[x] as int, b[y] as int),
            forall|y: int| 
                #[trigger] abs_diff_spec(a[i as int] as int, b[y] as int)
                && 0 <= y < j as int 
                ==> min_diff as int <= abs_diff_spec(a[i as int] as int, b[y] as int),
    {
        let diff = abs_diff_exec(a[i], b[j]);
        if diff < min_diff {
            min_diff = diff;
        }

        if a[i] < b[j] {
            i = i + 1;
        } else if a[i] > b[j] {
            j = j + 1;
        } else {
            return min_diff as u32;
        }
    }

    min_diff as u32
}
// </vc-code>

fn main() {}

}