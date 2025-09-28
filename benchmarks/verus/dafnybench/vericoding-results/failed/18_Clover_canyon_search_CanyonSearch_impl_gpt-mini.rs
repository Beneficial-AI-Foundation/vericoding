use vstd::prelude::*;

verus! {

// <vc-helpers>
// Helper lemma to bound absolute difference of two i32 values as an int
proof fn abs_diff_i32_bound(x: i32, y: i32)
    ensures if (x as int) < (y as int) {
        0 <= (y as int) - (x as int) && (y as int) - (x as int) <= 4294967295
    } else {
        0 <= (x as int) - (y as int) && (x as int) - (y as int) <= 4294967295
    }
{
    let xi = x as int;
    let yi = y as int;
    // bounds for i32 values when cast to mathematical int
    assert(xi <= 2147483647);
    assert(xi >= -2147483648);
    assert(yi <= 2147483647);
    assert(yi >= -2147483648);
    if xi < yi {
        // yi - xi <= 2147483647 - (-2147483648) = 4294967295
        assert(yi - xi <= 2147483647 - (-2147483648));
        assert(2147483647 - (-2147483648) == 4294967295);
        assert(0 <= yi - xi);
    } else {
        // xi - yi <= 2147483647 - (-2147483648) = 4294967295
        assert(xi - yi <= 2147483647 - (-2147483648));
        assert(2147483647 - (-2147483648) == 4294967295);
        assert(0 <= xi - yi);
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
    let n: int = a.len() as int;
    let m: int = b.len() as int;
    let nm: int = n * m;

    // We linearize the double loop by a single index k that ranges over 0..n*m - 1.
    // Start with k = 1 and initialize minv to the (0,0) pair so the invariant holds initially.
    let mut k: int = 1;
    let mut best_i: int = 0;
    let mut best_j: int = 0;
    let ai0: int = a[0usize] as int;
    let bj0: int = b[0usize] as int;
    let mut minv: int = if ai0 < bj0 { bj0 - ai0 } else { ai0 - bj0 };
    // bound proof for initial minv
    proof { abs_diff_i32_bound(a[0usize], b[0usize]); }

    // Invariant:
    // 1 <= k <= nm
    // best_i in [0,n), best_j in [0,m)
    // minv == diff(best_i,best_j)
    // for all p,q with 0<=p<n,0<=q<m and p*m+q < k => minv <= diff(p,q)
    while k < nm
        invariant 1 <= k && k <= nm;
        invariant 0 <= best_i && best_i < n;
        invariant 0 <= best_j && best_j < m;
        invariant minv ==
            (if (a[best_i as usize] as int) < (b[best_j as usize] as int) {
                (b[best_j as usize] as int) - (a[best_i as usize] as int)
            } else {
                (a[best_i as usize] as int) - (b[best_j as usize] as int)
            });
        invariant forall |p: int, q: int|
            0 <= p && p < n && 0 <= q && q < m && p * m + q < k ==>
                #[trigger] minv <= (if (a[p as usize] as int) < (b[q as usize] as int) {
                    (b[q as usize] as int) - (a[p as usize] as int)
                } else {
                    (a[p as usize] as int) - (b[q as usize] as int)
                });
        decreases nm - k;
    {
        // compute indices for the k-th pair
        let i: int = k / m;
        let j: int = k % m;
        // bounds: since k < n*m and m > 0, we have 0 <= i < n and 0 <= j < m
        assert(0 <= i);
        assert(i < n);
        assert(0 <= j);
        assert(j < m);

        let ai: int = a[i as usize] as int;
        let bj: int = b[j as usize] as int;
        let cur: int = if ai < bj { bj - ai } else { ai - bj };
        // bound for current difference
        proof { abs_diff_i32_bound(a[i as usize], b[j as usize]); }

        if cur < minv {
            minv = cur;
            best_i = i;
            best_j = j;
        }

        k = k + 1;
    }

    // After loop, k == nm and invariant ensures best indices are in range and minv equals diff(best_i,best_j)
    assert(0 <= best_i && best_i < n);
    assert(0 <= best_j && best_j < m);
    // Bound minv so we can cast to u32
    proof { abs_diff_i32_bound(a[best_i as usize], b[best_j as usize]); }
    assert(0 <= minv && minv <= 4294967295);

    (minv as u32)
}
// </vc-code>

fn main() {}

}