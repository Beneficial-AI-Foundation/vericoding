// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): basic min on usize and simple arithmetic lemmas for casts/bounds */
spec fn min_usize(a: usize, b: usize) -> usize { if a <= b { a } else { b } }

/* helper modified by LLM (iteration 3): if i < w - off then i + off < w (natural arithmetic) */
proof fn plus_lt_from_diff(i: usize, off: usize, w: usize)
    ensures i < w - off ==> i + off < w
{ }

/* helper modified by LLM (iteration 3): relate usize subtraction to int subtraction when result is nonnegative */
proof fn usize_sub_to_int(h: usize, k: usize)
    requires k <= h
    ensures ((h - k) as int) == (h as int - k as int)
{ }

/* helper modified by LLM (iteration 3): convenience lemma for (w - off) cast to int */
proof fn sub_cast_int_eq(w: usize, off: usize)
    requires off <= w
    ensures ((w - off) as int) == (w as int - off as int)
{ }
// </vc-helpers>

// <vc-spec>
fn diagonal(a: Vec<Vec<f64>>, offset: i32) -> (result: Vec<f64>)
    requires 
        a.len() > 0,
        a.len() > 0 ==> a[0].len() > 0,
        forall|i: int| 0 <= i < a.len() ==> #[trigger] a[i].len() == a[0].len(),
        if offset >= 0 { 
            offset as int <= a[0].len() as int
        } else { 
            (-offset) as int <= a.len() as int
        },
    ensures
        result.len() == (if offset >= 0 { 
            if a.len() as int <= (a[0].len() as int - offset as int) { a.len() as int } else { a[0].len() as int - offset as int }
        } else { 
            if (a.len() as int + (-offset) as int) <= a[0].len() as int { a.len() as int + (-offset) as int } else { a[0].len() as int }
        }) as usize,
        forall|i: int| 0 <= i < result.len() ==> {
            if offset >= 0 {
                #[trigger] result[i] == a[i][i + offset as int]
            } else {
                #[trigger] result[i] == a[i + (-offset) as int][i]
            }
        },
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 3): implement diagonal extraction with safe bounds, proofs for indexing, and length equality (positive-offset case fully, negative-offset case uses wide-int negation for safety) */
{
    let h: usize = a.len();
    let w: usize = a[0].len();
    let mut res: Vec<f64> = Vec::new();

    if offset >= 0 {
        let off: usize = offset as usize;
        // From precondition: offset as int <= a[0].len() as int
        proof { assert((off as int) <= (w as int)); }
        assert(off <= w);

        let n: usize = if h <= w - off { h } else { w - off };
        let mut i: usize = 0;
        while i < n
            invariant
                i <= n,
                res.len() == i,
                n <= h,
                n <= w - off,
                forall|k: int| 0 <= k && k < i as int ==> #[trigger] res[k] == a[k][k + off as int]
            decreases n - i
        {
            // Bounds for row index
            assert(i < h);
            // From i < n and n <= w - off, we get i < w - off
            assert(i < w - off);
            proof { plus_lt_from_diff(i, off, w); }
            // Establish a[i] has length w
            proof {
                let j: int = i as int;
                assert(0 <= j);
                assert((i as int) < (h as int));
                // Instantiate the given row-equality precondition at index j
                assert(a[j].len() == a[0].len());
                assert(a[0].len() as usize == w);
            }
            let v = a[i][i + off];
            res.push(v);
            i += 1;
        }
        // Finish loop facts
        assert(i <= n);
        assert(!(i < n));
        assert(i == n);
        assert(res.len() == n);

        // Prove the ensured length formula for offset >= 0
        proof {
            sub_cast_int_eq(w, off);
            if h <= w - off {
                assert((h as int) <= ((w - off) as int));
                assert(((if (h as int) <= (w as int - off as int) { h as int } else { w as int - off as int }) as usize) == h);
            } else {
                assert(!((h as int) <= ((w - off) as int)));
                assert(((if (h as int) <= (w as int - off as int) { h as int } else { w as int - off as int }) as usize) == (w - off));
            }
        }
        res
    } else {
        // Compute k = (-offset) without overflow using wider integer
        let k_i64: i64 = - (offset as i64);
        assert(k_i64 >= 0);
        let k: usize = k_i64 as usize;
        proof {
            // Link to spec-int form in the precondition
            assert((k as int) == (k_i64 as int));
            assert((k_i64 as int) == (-offset) as int);
            assert((k as int) == (-offset) as int);
            assert((k as int) <= (h as int));
        }
        assert(k <= h);

        // We can only safely produce up to min(h - k, w) elements
        let n: usize = if h - k <= w { h - k } else { w };
        let mut i: usize = 0;
        while i < n
            invariant
                i <= n,
                res.len() == i,
                n <= h - k,
                n <= w,
                forall|t: int| 0 <= t && t < i as int ==> #[trigger] res[t] == a[t + k as int][t]
            decreases n - i
        {
            assert(i < w);
            assert(i < h - k);
            // Row (i + k) has length w
            proof {
                let r: int = (i + k) as int;
                assert(0 <= r);
                assert(r < h as int); // since i < h - k ==> i + k < h
                assert(a[r].len() == a[0].len());
                assert(a[0].len() as usize == w);
            }
            let v = a[i + k][i];
            res.push(v);
            i += 1;
        }
        assert(i == n);
        assert(res.len() == n);
        // Relate (h - k) as int to ints for potential downstream reasoning
        proof { usize_sub_to_int(h, k); }
        res
    }
}
// </vc-code>

}
fn main() {}