use vstd::prelude::*;

verus! {

// <vc-helpers>
fn binary_search_square_root(n: u32) -> (r: u32)
  ensures r * r <= n < (r + 1) * (r + 1)
{
  if n == 0 {
    0
  } else {
    let mut low: u32 = 0;
    let mut high: u32 = 65536;
    
    while low < high 
      invariant 
        low <= high,
        forall |x: u32| x < low ==> x * x <= n,
        high * high > n,
    {
      let mid = low + (high - low) / 2;
      if mid * mid <= n {
        low = mid + 1;
      } else {
        high = mid;
      }
    }
    
    low - 1
  }
}
// </vc-helpers>

// <vc-spec>
fn square_root(n: u32) -> (r: u32)
  ensures r * r <= n < (r + 1) * (r + 1)
// </vc-spec>
// <vc-code>
{
  binary_search_square_root(n)
}
// </vc-code>

fn main() {}

}