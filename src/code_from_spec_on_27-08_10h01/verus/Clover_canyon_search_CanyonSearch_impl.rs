use vstd::prelude::*;

verus! {

// <vc-helpers>
spec fn abs_diff(x: i32, y: i32) -> int {
    if x < y { y - x } else { x - y }
}

proof fn lemma_abs_diff_nonneg(x: i32, y: i32)
    ensures abs_diff(x, y) >= 0
{
}

proof fn lemma_abs_diff_symmetric(x: i32, y: i32)
    ensures abs_diff(x, y) == abs_diff(y, x)
{
}

proof fn lemma_min_distance_exists(a: &[i32], b: &[i32], min_d: int)
    requires 
        a.len() != 0 && b.len() != 0,
        forall|i: int, j: int| 0 <= i < a.len() && 0 <= j < b.len() ==> 
            min_d <= abs_diff(a[i], b[j]),
        exists|i: int, j: int| 0 <= i < a.len() && 0 <= j < b.len() && 
            min_d == abs_diff(a[i], b[j])
    ensures 
        forall|i: int, j: int| 0 <= i < a.len() && 0 <= j < b.len() ==> 
            min_d <= abs_diff(a[i], b[j])
{
}

spec fn abs_diff_nat(x: i32, y: i32) -> nat {
    abs_diff(x, y) as nat
}

proof fn lemma_abs_diff_cast_valid(x: i32, y: i32)
    ensures abs_diff(x, y) >= 0,
        abs_diff_nat(x, y) == abs_diff(x, y)
{
    lemma_abs_diff_nonneg(x, y);
}

proof fn lemma_abs_diff_fits_u32(x: i32, y: i32)
    ensures abs_diff(x, y) <= u32::MAX as int
{
    lemma_abs_diff_nonneg(x, y);
    if x < y {
        assert(y - x <= i32::MAX as int);
    } else {
        assert(x - y <= i32::MAX as int);
    }
}
// </vc-helpers>

// <vc-spec>
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
// </vc-spec>

// <vc-code>
{
    let ghost abs_diff_initial = abs_diff(a[0 as int], b[0 as int]);
    proof {
        lemma_abs_diff_cast_valid(a[0 as int], b[0 as int]);
        lemma_abs_diff_fits_u32(a[0 as int], b[0 as int]);
    }
    let mut min_distance = abs_diff_initial as u32;
    let mut i = 0;
    
    while i < a.len() 
        invariant
            0 <= i <= a.len(),
            min_distance >= 0,
            exists|ii: int, jj: int| 0 <= ii < a.len() && 0 <= jj < b.len() && 
                min_distance as int == abs_diff(a[ii], b[jj]),
            forall|ii: int, jj: int| 0 <= ii < i && 0 <= jj < b.len() ==> 
                min_distance as int <= abs_diff(a[ii], b[jj]),
    {
        let mut j = 0;
        
        while j < b.len()
            invariant
                0 <= i < a.len(),
                0 <= j <= b.len(),
                min_distance >= 0,
                exists|ii: int, jj: int| 0 <= ii < a.len() && 0 <= jj < b.len() && 
                    min_distance as int == abs_diff(a[ii], b[jj]),
                forall|ii: int, jj: int| 0 <= ii < i && 0 <= jj < b.len() ==> 
                    min_distance as int <= abs_diff(a[ii], b[jj]),
                forall|jj: int| 0 <= jj < j ==> 
                    min_distance as int <= abs_diff(a[i as int], b[jj]),
        {
            let ghost current_abs_diff = abs_diff(a[i as int], b[j as int]);
            proof {
                lemma_abs_diff_cast_valid(a[i as int], b[j as int]);
                lemma_abs_diff_fits_u32(a[i as int], b[j as int]);
            }
            let current_distance = current_abs_diff as u32;
            
            if current_distance < min_distance {
                min_distance = current_distance;
            }
            
            j += 1;
        }
        
        i += 1;
    }
    
    proof {
        assert(forall|ii: int, jj: int| 0 <= ii < a.len() && 0 <= jj < b.len() ==> 
            min_distance as int <= abs_diff(a[ii], b[jj]));
    }
    
    min_distance
}
// </vc-code>

fn main() {}

}