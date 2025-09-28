use vstd::prelude::*;

verus! {

// <vc-helpers>
fn abs_diff(x: i32, y: i32) -> u32 {
  if x < y {
    (y - x) as u32
  } else {
    (x - y) as u32
  }
}

proof fn lemma_abs_diff_comm(x: i32, y: i32)
  ensures abs_diff(x, y) == abs_diff(y, x)
{
  if x < y {
    assert(abs_diff(x, y) == (y - x) as u32);
    assert(abs_diff(y, x) == (y - x) as u32);
  } else {
    assert(abs_diff(x, y) == (x - y) as u32);
    assert(abs_diff(y, x) == (x - y) as u32);
  }
}

proof fn lemma_abs_diff_triangle(x: i32, y: i32, z: i32)
  ensures abs_diff(x, z) <= abs_diff(x, y) + abs_diff(y, z)
{
  if x < z {
    if x < y {
      if y < z {
        assert((z - y) + (y - x) == z - x);
        assert(abs_diff(x, z) == (z - x) as u32);
        assert(abs_diff(x, y) == (y - x) as u32);
        assert(abs_diff(y, z) == (z - y) as u32);
      } else {
        assert(y >= z);
        assert(abs_diff(x, z) == (z - x) as u32);
        assert(abs_diff(x, y) == (y - x) as u32);
        assert(abs_diff(y, z) == (y - z) as u32);
        assert((z - x) <= (y - x) + (y - z));
      }
    } else {
      assert(y <= x);
      assert(abs_diff(x, z) == (z - x) as u32);
      assert(abs_diff(x, y) == (x - y) as u32);
      assert(abs_diff(y, z) == if y < z { (z - y) as u32 } else { (y - z) as u32 });
      assert((z - x) <= (x - y) + (if y < z { (z - y) } else { (y - z) }));
    }
  } else {
    assert(x >= z);
    if x < y {
      assert(abs_diff(x, z) == (x - z) as u32);
      assert(abs_diff(x, y) == (y - x) as u32);
      assert(abs_diff(y, z) == if y < z { (z - y) as u32 } else { (y - z) as u32 });
      assert((x - z) <= (y - x) + (if y < z { (z - y) } else { (y - z) }));
    } else {
      assert(y <= x);
      if y < z {
        assert(abs_diff(x, z) == (x - z) as u32);
        assert(abs_diff(x, y)
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
fn abs_diff(x: i32, y: i32) -> u32 {
  if x < y {
    (y - x) as u32
  } else {
    (x - y) as u32
  }
}

proof fn lemma_abs_diff_comm(x: i32, y: i32)
  ensures abs_diff(x, y) == abs_diff(y, x)
{
  if x < y {
    assert(abs_diff(x, y) == (y - x) as u32);
    assert(abs_diff(y, x) == (y - x) as u32);
  } else {
    assert(abs_diff(x, y) == (x - y) as u32);
    assert(abs_diff(y, x) == (x - y) as u32);
  }
}

proof fn lemma_abs_diff_triangle(x: i32, y: i32, z: i32)
  ensures abs_diff(x, z) <= abs_diff(x, y) + abs_diff(y, z)
{
  if x < z {
    if x < y {
      if y < z {
        assert((z - y) + (y - x) == z - x);
        assert(abs_diff(x, z) == (z - x) as u32);
        assert(abs_diff(x, y) == (y - x) as u32);
        assert(abs_diff(y, z) == (z - y) as u32);
      } else {
        assert(y >= z);
        assert(abs_diff(x, z) == (z - x) as u32);
        assert(abs_diff(x, y) == (y - x) as u32);
        assert(abs_diff(y, z) == (y - z) as u32);
        assert((z - x) <= (y - x) + (y - z));
      }
    } else {
      assert(y <= x);
      assert(abs_diff(x, z) == (z - x) as u32);
      assert(abs_diff(x, y) == (x - y) as u32);
      assert(abs_diff(y, z) == if y < z { (z - y) as u32 } else { (y - z) as u32 });
      assert((z - x) <= (x - y) + (if y < z { (z - y) } else { (y - z) }));
    }
  } else {
    assert(x >= z);
    if x < y {
      assert(abs_diff(x, z) == (x - z) as u32);
      assert(abs_diff(x, y) == (y - x) as u32);
      assert(abs_diff(y, z) == if y < z { (z - y) as u32 } else { (y - z) as u32 });
      assert((x - z) <= (y - x) + (if y < z { (z - y) } else { (y - z) }));
    } else {
      assert(y <= x);
      if y < z {
        assert(abs_diff(x, z) == (x - z) as u32);
        assert(abs_diff(x, y)
// </vc-code>

fn main() {}

}