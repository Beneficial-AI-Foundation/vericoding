// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): create a Vec<char> of length n filled with '0' */
fn replicate_zeros(n: usize) -> (res: Vec<char>)
    ensures
        res.len() == n,
        all_zeros(res@)
{
    let mut res: Vec<char> = Vec::new();
    let mut i: usize = 0usize;
    while i < n
        invariant
            0 <= i && i <= n,
            res.len() == i,
            forall|k: int| 0 <= k < i as int ==> #[trigger] res@[k] == '0',
        decreases n - i
    {
        res.push('0');
        i += 1usize;
    }
    res
}
// </vc-helpers>

// <vc-spec>
spec fn is_sign_char(c: char) -> bool {
    c == '+' || c == '-'
}

spec fn all_zeros(s: Seq<char>) -> bool {
    forall|i: int| 0 <= i < s.len() ==> s[i] == '0'
}

spec fn max_usize(a: usize, b: usize) -> usize {
    if a >= b { a } else { b }
}

fn zfill(a: Vec<Vec<char>>, width: usize) -> (result: Vec<Vec<char>>)
    ensures
        result.len() == a.len(),
        forall|i: int| 0 <= i < result.len() ==> 
            #[trigger] result[i].len() == max_usize(a[i].len(), width),
        forall|i: int| 0 <= i < result.len() && a[i].len() >= width ==> 
            #[trigger] result[i]@ == a[i]@,
        forall|i: int| 0 <= i < result.len() && a[i].len() < width && a[i].len() > 0 && 
            !is_sign_char(a[i]@[0]) ==> 
            #[trigger] all_zeros(result[i]@.take((width - a[i].len()) as int)) &&
            result[i]@.skip((width - a[i].len()) as int) == a[i]@,
        forall|i: int| 0 <= i < result.len() && a[i].len() < width && a[i].len() > 0 && 
            is_sign_char(a[i]@[0]) ==> 
            #[trigger] result[i]@[0] == a[i]@[0] &&
            result[i]@.skip(width as int) == a[i]@.skip(1),
        forall|i: int| 0 <= i < result.len() && a[i].len() == 0 ==> 
            #[trigger] result[i].len() == width && 
            all_zeros(result[i]@),
        forall|i: int| 0 <= i < result.len() && a[i].len() < width ==> 
            #[trigger] result[i].len() == width,
        forall|i: int| 0 <= i < result.len() && a[i].len() < width ==> 
            #[trigger] all_zeros(result[i]@.take((width - a[i].len()) as int))
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): add per-index invariants and prove contents for each constructed row before pushing */
    let mut result: Vec<Vec<char>> = Vec::new();
    let mut i: usize = 0usize;
    while i < a.len()
        invariant
            0 <= i && i <= a.len(),
            result.len() == i,
            forall|k: int| 0 <= k < i ==> #[trigger] result[k].len() == max_usize(a[k].len(), width),
            forall|k: int| 0 <= k < i && a[k].len() >= width ==> #[trigger] result[k]@ == a[k]@,
            forall|k: int| 0 <= k < i && a[k].len() < width && a[k].len() > 0 && !is_sign_char(a[k]@[0]) ==> #[trigger] all_zeros(result[k]@.take((width - a[k].len()) as int)) && result[k]@.skip((width - a[k].len()) as int) == a[k]@,
            forall|k: int| 0 <= k < i && a[k].len() < width && a[k].len() > 0 && is_sign_char(a[k]@[0]) ==> #[trigger] result[k]@[0] == a[k]@[0] && result[k]@.skip(width as int) == a[k]@.skip(1),
            forall|k: int| 0 <= k < i && a[k].len() == 0 ==> #[trigger] result[k].len() == width && all_zeros(result[k]@),
            forall|k: int| 0 <= k < i && a[k].len() < width ==> #[trigger] result[k].len() == width,
            forall|k: int| 0 <= k < i && a[k].len() < width ==> #[trigger] all_zeros(result[k]@.take((width - a[k].len()) as int)),
        decreases a.len() - i
    {
        let row = &a[i];
        let mut cur: Vec<char> = Vec::new();
        if row.len() >= width {
            let mut j: usize = 0usize;
            while j < row.len()
                invariant
                    0 <= j && j <= row.len(),
                    cur.len() == j,
                    forall|k: int| 0 <= k < j as int ==> #[trigger] cur@[k] == row@[k],
                decreases row.len() - j
            {
                cur.push(row[j]);
                j += 1usize;
            }
            proof {
                assert(cur.len() == row.len());
                assert(forall|k: int| 0 <= k < row.len() as int ==> cur@[k] == row@[k]);
            }
        } else {
            if row.len() == 0 {
                cur = replicate_zeros(width);
            } else {
                let pad = width - row.len();
                if row[0] == '+' || row[0] == '-' {
                    cur.push(row[0]);
                    let mut z: usize = 0usize;
                    while z < pad
                        invariant
                            0 <= z && z <= pad,
                            cur.len() == 1 + z,
                            cur@[0] == row@[0],
                            forall|k: int| 0 <= k < z as int ==> #[trigger] cur@[1 + k] == '0',
                        decreases pad - z
                    {
                        cur.push('0');
                        z += 1usize;
                    }
                    let mut t: usize = 1usize;
                    while t < row.len()
                        invariant
                            1 <= t && t <= row.len(),
                            cur.len() == 1 + pad + (t - 1),
                            cur@[0] == row@[0],
                            forall|k: int| 0 <= k < pad as int ==> #[trigger] cur@[1 + k] == '0',
                            forall|k: int| 0 <= k < (t - 1) as int ==> #[trigger] cur@[1 + pad + k] == row@[1 + k],
                        decreases row.len() - t
                    {
                        cur.push(row[t]);
                        t += 1usize;
                    }
                } else {
                    let mut z: usize = 0usize;
                    while z < pad
                        invariant
                            0 <= z && z <= pad,
                            cur.len() == z,
                            forall|k: int| 0 <= k < z as int ==> #[trigger] cur@[k] == '0',
                        decreases pad - z
                    {
                        cur.push('0');
                        z += 1usize;
                    }
                    let mut t: usize = 0usize;
                    while t < row.len()
                        invariant
                            0 <= t && t <= row.len(),
                            cur.len() == pad + t,
                            forall|k: int| 0 <= k < pad as int ==> #[trigger] cur@[k] == '0',
                            forall|k: int| 0 <= k < t as int ==> #[trigger] cur@[pad + k] == row@[k],
                        decreases row.len() - t
                    {
                        cur.push(row[t]);
                        t += 1usize;
                    }
                }
            }
        }
        proof {
            if row.len() >= width {
                assert(cur.len() == row.len());
                assert(cur@ == row@);
            } else {
                assert(cur.len() == width);
                if row.len() == 0 {
                    assert(all_zeros(cur@));
                } else {
                    if row[0] == '+' || row[0] == '-' {
                        assert(cur@[0] == row@[0]);
                        assert(cur@.skip(width as int) == row@.skip(1));
                        assert(all_zeros(cur@.take((width - row.len()) as int)));
                    } else {
                        assert(cur@.skip((width - row.len()) as int) == row@);
                        assert(all_zeros(cur@.take((width - row.len()) as int)));
                    }
                }
            }
        }
        result.push(cur);
        i += 1usize;
    }
    result
}
// </vc-code>


}
fn main() {}