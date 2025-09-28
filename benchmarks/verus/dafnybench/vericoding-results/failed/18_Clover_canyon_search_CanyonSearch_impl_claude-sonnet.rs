use vstd::prelude::*;

verus! {

// <vc-helpers>
fn abs_diff(x: i32, y: i32) -> (result: u32)
    requires
        x - y >= i32::MIN && y - x >= i32::MIN
    ensures
        result as int == if x < y { y - x } else { x - y }
{
    if x < y {
        assert(y >= x);
        assert(y - x >= 0);
        assert(y - x <= u32::MAX);
        let diff = (y - x) as u32;
        assert(diff as int == y - x);
        diff
    } else {
        assert(x >= y);
        assert(x - y >= 0);
        assert(x - y <= u32::MAX);
        let diff = (x - y) as u32;
        assert(diff as int == x - y);
        diff
    }
}

proof fn abs_diff_precondition_for_i32(x: i32, y: i32)
    ensures x - y >= i32::MIN && y - x >= i32::MIN
{
    assert(i32::MIN == -2147483648);
    assert(i32::MAX == 2147483647);
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
    proof {
        abs_diff_precondition_for_i32(a[0], b[0]);
    }
    let mut min_diff = abs_diff(a[0], b[0]);
    let mut i = 0;
    let mut j = 0;
    
    while i < a.len() && j < b.len()
        invariant
            0 <= i <= a.len(),
            0 <= j <= b.len(),
            (i < a.len() || j < b.len()),
            exists|ii: int, jj: int| 0 <= ii < a.len() && 0 <= jj < b.len() && 
                min_diff as int == (if a[ii] < b[jj] { 
                    b[jj] - a[ii]
                } else { 
                    a[ii] - b[jj]
                }),
            forall|ii: int, jj: int| 0 <= ii <= i && 0 <= jj < b.len() && !(ii == i && j < b.len()) ==> 
                min_diff as int <= (if a[ii] < b[jj] { 
                    b[jj] - a[ii]
                } else { 
                    a[ii] - b[jj]
                }),
            forall|ii: int, jj: int| 0 <= ii < a.len() && 0 <= jj <= j && !(jj == j && i < a.len()) ==> 
                min_diff as int <= (if a[ii] < b[jj] { 
                    b[jj] - a[ii]
                } else { 
                    a[ii] - b[jj]
                }),
        decreases (a.len() - i) + (b.len() - j)
    {
        proof {
            abs_diff_precondition_for_i32(a[i], b[j]);
        }
        let current_diff = abs_diff(a[i], b[j]);
        if current_diff < min_diff {
            min_diff = current_diff;
        }
        
        if a[i] < b[j] {
            i += 1;
        } else {
            j += 1;
        }
    }
    
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            j == b.len(),
            exists|ii: int, jj: int| 0 <= ii < a.len() && 0 <= jj < b.len() && 
                min_diff as int == (if a[ii] < b[jj] { 
                    b[jj] - a[ii]
                } else { 
                    a[ii] - b[jj]
                }),
            forall|ii: int, jj: int| 0 <= ii < a.len() && 0 <= jj < b.len() ==> 
                min_diff as int <= (if a[ii] < b[jj] { 
                    b[jj] - a[ii]
                } else { 
                    a[ii] - b[jj]
                }),
        decreases a.len() - i
    {
        proof {
            abs_diff_precondition_for_i32(a[i], b[j-1]);
        }
        let current_diff = abs_diff(a[i], b[j-1]);
        if current_diff < min_diff {
            min_diff = current_diff;
        }
        i += 1;
    }
    
    while j < b.len()
        invariant
            i == a.len(),
            0 <= j <= b.len(),
            exists|ii: int, jj: int| 0 <= ii < a.len() && 0 <= jj < b.len() && 
                min_diff as int == (if a[ii] < b[jj] { 
                    b[jj] - a[ii]
                } else { 
                    a[ii] - b[jj]
                }),
            forall|ii: int, jj: int| 0 <= ii < a.len() && 0 <= jj < b.len() ==> 
                min_diff as int <= (if a[ii] < b[jj] { 
                    b[jj] - a[ii]
                } else { 
                    a[ii] - b[jj]
                }),
        decreases b.len() - j
    {
        proof {
            abs_diff_precondition_for_i32(a[i-1], b[j]);
        }
        let current_diff = abs_diff(a[i-1], b[j]);
        if current_diff < min_diff {
            min_diff = current_diff;
        }
        j += 1;
    }
    
    min_diff
}
// </vc-code>

fn main() {}

}