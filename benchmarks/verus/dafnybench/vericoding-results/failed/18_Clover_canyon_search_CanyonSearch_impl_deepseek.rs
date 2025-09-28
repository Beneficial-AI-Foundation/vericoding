use vstd::prelude::*;

verus! {

// <vc-helpers>
proof fn lemma_abs_diff_property(x: int, y: int) 
    ensures
        (if x < y { y - x } else { x - y }) >= 0
{
}

proof fn lemma_monotonic_inequality(a: Seq<int>, b: Seq<int>, i: int, j: int, k: int, l: int)
    requires
        0 <= i <= j < a.len(),
        0 <= k <= l < b.len(),
        forall|p: int, q: int| 0 <= p < q < a.len() ==> a[p] <= a[q],
        forall|p: int, q: int| 0 <= p < q < b.len() ==> b[p] <= b[q],
    ensures
        (if a[i] < b[k] { b[k] - a[i] } else { a[i] - b[k] }) <= (if a[j] < b[l] { b[l] - a[j] } else { a[j] - b[l] })
{
}

spec fn abs_diff(x: int, y: int) -> int {
    if x < y {
        y - x
    } else {
        x - y
    }
}

spec fn find_min_abs_diff(a: Seq<int>, b: Seq<int>, i: int, j: int) -> bool
    recommends
        i >= 0,
        j >= 0
{
    &&& i < a.len()
    &&& j < b.len()
    &&& forall|p: int, q: int| 
        0 <= p < a.len() && 0 <= q < b.len() ==> 
        abs_diff(a[i], b[j]) <= abs_diff(a[p], b[q])
}

proof fn lemma_abs_diff_nonnegative(x: int, y: int)
    ensures
        abs_diff(x, y) >= 0
{
    lemma_abs_diff_property(x, y);
}

proof fn lemma_abs_diff_u32_conversion(x: int, y: int)
    requires
        abs_diff(x, y) >= 0,
    ensures
        (abs_diff(x, y) as u32) as int == abs_diff(x, y)
{
}

spec fn abs_diff_i32(x: i32, y: i32) -> i32 {
    if x < y {
        y - x
    } else {
        x - y
    }
}

spec fn abs_diff_u32(x: i32, y: i32) -> u32 {
    if x < y {
        (y - x) as u32
    } else {
        (x - y) as u32
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
  let mut i: usize = 0;
  let mut j: usize = 0;
  
  proof {
    lemma_abs_diff_property(a@[0] as int, b@[0] as int);
  }
  
  let current_diff = abs_diff_u32(a[0], b[0]);
  let mut d: u32 = current_diff;
  
  let mut min_i = 0;
  let mut min_j = 0;
  
  while i < a.len() && j < b.len()
      invariant
          0 <= i <= a.len(),
          0 <= j <= b.len(),
          exists|p: int, q: int| 0 <= p <= i && 0 <= q <= j && find_min_abs_diff(a@, b@, p, q),
          forall|p: int, q: int| 0 <= p < a.len() && 0 <= q < b.len() ==> 
              d as int <= abs_diff(a@[p] as int, b@[q] as int),
  {
      let current_diff_val = abs_diff_u32(a[i], b[j]);
      
      proof {
          lemma_abs_diff_nonnegative(a@[i] as int, b@[j] as int);
      }
      
      if current_diff_val < d {
          proof {
              lemma_abs_diff_u32_conversion(a@[i] as int, b@[j] as int);
          }
          d = current_diff_val;
          min_i = i;
          min_j = j;
      }
      
      if a[i] < b[j] {
          if i < a.len() - 1 {
              i += 1;
          } else {
              j += 1;
          }
      } else {
          if j < b.len() - 1 {
              j += 1;
          } else {
              i += 1;
          }
      }
  }
  
  proof {
      assert(find_min_abs_diff(a@, b@, min_i, min_j));
      assert(d as int == abs_diff(a@[min_i] as int, b@[min_j] as int));
  }
  
  d
}
// </vc-code>

fn main() {}

}