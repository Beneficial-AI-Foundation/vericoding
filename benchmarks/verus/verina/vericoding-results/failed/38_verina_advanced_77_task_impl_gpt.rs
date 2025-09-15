// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): keep min/max on usize and a lemma stating min is at least a common lower bound */
spec fn max_usize(a: usize, b: usize) -> usize { if a >= b { a } else { b } }
spec fn min_usize(a: usize, b: usize) -> usize { if a <= b { a } else { b } }
proof fn lemma_min_ge_if(a: usize, b: usize, x: usize)
    requires a >= x, b >= x
    ensures min_usize(a, b) >= x
{ }

// </vc-helpers>

// <vc-spec>
fn trap_rain_water(height: &Vec<usize>) -> (result: usize)
    requires height.len() >= 0,
    ensures result >= 0,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): add assert to prevent underflow in subtraction and keep loop invariants */
    let n = height.len();
    if n <= 2 {
        return 0;
    }
    assert(n >= 3);

    let mut left: Vec<usize> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant i <= n && left.len() == i && n == height.len()
        decreases n - i
    {
        assert(i < height.len());
        if i == 0 {
            left.push(height[i]);
        } else {
            assert(i >= 1);
            assert(left.len() == i);
            assert(i - 1 < left.len());
            let prev = left[i - 1];
            let cur_h = height[i];
            let lm = if prev >= cur_h { prev } else { cur_h };
            left.push(lm);
        }
        i += 1;
    }

    let mut rev_right: Vec<usize> = Vec::new();
    let mut j: usize = n;
    while j > 0
        invariant j <= n && rev_right.len() == n - j && n == height.len()
        decreases j
    {
        let idx = j - 1;
        assert(idx < height.len());
        if j == n {
            rev_right.push(height[idx]);
        } else {
            assert(rev_right.len() == n - j);
            assert(rev_right.len() >= 1);
            assert(rev_right.len() - 1 < rev_right.len());
            let prev = rev_right[rev_right.len() - 1];
            let cur_h = height[idx];
            let rm = if prev >= cur_h { prev } else { cur_h };
            rev_right.push(rm);
        }
        j -= 1;
    }

    assert(left.len() == n);
    assert(rev_right.len() == n);

    let mut water: usize = 0;
    let mut k: usize = 0;
    while k < n
        invariant k <= n && left.len() == n && rev_right.len() == n && n == height.len()
        decreases n - k
    {
        assert(k < n);
        assert(k < left.len());
        let idx = n - 1 - k;
        assert(idx < rev_right.len());
        assert(k < height.len());
        let lm = left[k];
        let rm = rev_right[idx];
        let m = if lm <= rm { lm } else { rm };
        let h = height[k];
        if m > h {
            assert(m >= h);
            let add = m - h;
            water = water + add;
        }
        k += 1;
    }
    water
}
// </vc-code>

}
fn main() {}