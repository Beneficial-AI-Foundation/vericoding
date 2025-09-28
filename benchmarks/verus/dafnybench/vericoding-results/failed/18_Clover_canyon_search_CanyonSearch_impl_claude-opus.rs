use vstd::prelude::*;

verus! {

// <vc-helpers>
proof fn abs_diff_monotonic(a: &[i32], b: &[i32], i1: int, j1: int, i2: int, j2: int)
    requires
        0 <= i1 <= i2 < a.len(),
        0 <= j1 <= j2 < b.len(),
        forall|i: int, j: int| 0 <= i < j < a.len() ==> a[i] <= a[j],
        forall|i: int, j: int| 0 <= i < j < b.len() ==> b[i] <= b[j],
    ensures
        a[i1] <= a[i2],
        b[j1] <= b[j2],
        a[i1] <= b[j1] ==> a[i2] - b[j2] >= a[i1] - b[j1] || b[j2] - a[i2] >= b[j1] - a[i1],
        a[i1] > b[j1] ==> a[i2] - b[j2] >= a[i1] - b[j1] || b[j2] - a[i2] >= a[i1] - b[j1],
{
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
    let mut min_diff: u32 = if a[0] < b[0] { 
        (b[0] - a[0]) as u32 
    } else { 
        (a[0] - b[0]) as u32 
    };
    let mut min_i: usize = 0;
    let mut min_j: usize = 0;

    while i < a.len() && j < b.len()
        invariant
            0 <= i <= a.len(),
            0 <= j <= b.len(),
            i < a.len() || j < b.len(),
            0 <= min_i < a.len(),
            0 <= min_j < b.len(),
            min_diff as int == (if a[min_i as int] < b[min_j as int] { 
                b[min_j as int] - a[min_i as int] 
            } else { 
                a[min_i as int] - b[min_j as int] 
            }),
            // We've checked all pairs (ii, jj) where ii < i and jj < j
            forall|ii: int, jj: int| 0 <= ii < i && 0 <= jj < j ==>
                min_diff as int <= (if a[ii] < b[jj] { b[jj] - a[ii] } else { a[ii] - b[jj] }),
            // We've checked all pairs with ii < i and any valid jj
            forall|ii: int, jj: int| 0 <= ii < i && 0 <= jj < b.len() && (j == 0 || a[ii] <= b[j-1]) ==>
                min_diff as int <= (if a[ii] < b[jj] { b[jj] - a[ii] } else { a[ii] - b[jj] }),
            // We've checked all pairs with jj < j and any valid ii
            forall|ii: int, jj: int| 0 <= jj < j && 0 <= ii < a.len() && (i == 0 || b[jj] <= a[i-1]) ==>
                min_diff as int <= (if a[ii] < b[jj] { b[jj] - a[ii] } else { a[ii] - b[jj] }),
    {
        let curr_diff = if a[i] < b[j] { 
            (b[j] - a[i]) as u32 
        } else { 
            (a[i] - b[j]) as u32 
        };
        
        if curr_diff < min_diff {
            min_diff = curr_diff;
            min_i = i;
            min_j = j;
        }

        if i + 1 < a.len() && (j + 1 >= b.len() || a[i] < b[j]) {
            i = i + 1;
        } else if j + 1 < b.len() {
            j = j + 1;
        } else {
            break;
        }
    }

    proof {
        assert forall|ii: int, jj: int| 0 <= ii < a.len() && 0 <= jj < b.len() implies
            min_diff as int <= (if a[ii] < b[jj] { b[jj] - a[ii] } else { a[ii] - b[jj] }) by {
            
            if ii < i && jj < j {
                // Already covered by loop invariant
            } else if ii >= i && jj >= j {
                // These pairs have differences >= current (i,j) pair due to monotonicity
                if ii > i {
                    assert(a[ii] >= a[i as int]);
                }
                if jj > j {
                    assert(b[jj] >= b[j as int]);
                }
                abs_diff_monotonic(a, b, i as int, j as int, ii, jj);
            } else if ii < i && jj >= j {
                // These were covered when we advanced j
                if j > 0 && a[ii] <= b[j-1] {
                    // This case was already checked by invariant
                } else if jj == j {
                    // We just checked (i,j)
                } else {
                    // jj > j, so b[jj] >= b[j]
                    assert(b[jj] >= b[j as int]);
                    if j > 0 {
                        abs_diff_monotonic(a, b, ii, j as int, ii, jj);
                    }
                }
            } else if ii >= i && jj < j {
                // These were covered when we advanced i
                if i > 0 && b[jj] <= a[i-1] {
                    // This case was already checked by invariant
                } else if ii == i {
                    // We just checked (i,j)
                } else {
                    // ii > i, so a[ii] >= a[i]
                    assert(a[ii] >= a[i as int]);
                    if i > 0 {
                        abs_diff_monotonic(a, b, i as int, jj, ii, jj);
                    }
                }
            }
        }
    }

    min_diff
}
// </vc-code>

fn main() {}

}