// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): build a zero vector of i8 with proper invariants */
fn zero_vec_i8(n: usize) -> (v: Vec<i8>)
    ensures
        v.len() == n as int,
        forall|k: int| 0 <= k < v.len() ==> v[k] == 0,
{
    let mut v: Vec<i8> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            v.len() == i as int,
            i <= n,
            forall|k: int| 0 <= k < v.len() ==> v[k] == 0,
        decreases (n - i) as int
    {
        v.push(0i8);
        i += 1;
    }
    v
}

/* helper modified by LLM (iteration 5): exact division into i8 when possible, with conditional guarantee */
fn div_if_exact_i8(num_i8: i8, den_i8: i8) -> (y: i8)
    ensures
        den_i8 as int != 0 ==> (
            let num: int = -(num_i8 as int);
            let den: int = den_i8 as int;
            (num % den == 0 && -128 <= num / den && num / den <= 127) ==> y as int * den == num
        ),
{
    if den_i8 != 0i8 {
        let num: int = 0 - num_i8 as int;
        let den: int = den_i8 as int;
        if num % den == 0 {
            let q = num / den;
            if -128 <= q && q <= 127 {
                return q as i8;
            }
        }
    }
    0i8
}

/* helper modified by LLM (iteration 5): safe negation for i8 with -128 guard */
fn safe_neg_i8(x: i8) -> (y: i8)
    ensures
        (x as int != -128) ==> (y as int == -(x as int)),
        (x as int == -128) ==> (y == 0i8),
{
    if x == -128i8 { 0i8 } else { 0i8 - x }
}
// </vc-helpers>

// <vc-spec>
fn polycompanion(c: Vec<i8>) -> (result: Vec<Vec<i8>>)
    requires 
        c.len() >= 2,
        c[c.len() - 1] != 0,
    ensures
        result.len() == c.len() - 1,
        forall|i: int| 0 <= i < result.len() ==> result[i].len() == c.len() - 1,
        forall|i: int, j: int| 
            0 <= i < result.len() && 0 <= j < result[i].len() ==>
            (if i + 1 == j && i < c.len() - 2 {
                result[i][j] as int == 1
            } else if i == c.len() - 2 {
                result[i][j] as int * c[c.len() - 1] as int == -c[j] as int
            } else {
                result[i][j] as int == 0
            })
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): use int indices to avoid usize overflow; construct rows with superdiagonal ones and last row using exact division when possible */
    let n: int = c.len();
    let m: int = n - 1;
    let mut result: Vec<Vec<i8>> = Vec::new();

    let mut i: int = 0;
    while i < m
        invariant
            0 <= i <= m,
            result.len() == i,
            m == c.len() - 1,
            c.len() >= 2,
            forall|p: int| 0 <= p < result.len() ==> result[p].len() == m,
        decreases m - i
    {
        let mut row: Vec<i8> = Vec::new();
        let mut j: int = 0;
        while j < m
            invariant
                0 <= j <= m,
                row.len() == j,
                m == c.len() - 1,
                c.len() >= 2,
            decreases m - j
        {
            let val: i8;
            if i < m - 1 && j == i + 1 {
                // superdiagonal ones for rows except the last
                val = 1i8;
            } else if i == m - 1 {
                // last row: aim for value y such that y * c_last == -c[j]
                let cl: i8 = c[(n - 1) as usize];
                let cj: i8 = c[j as usize];
                // Try exact division when possible and within i8 range; otherwise fall back to special simple cases
                let mut y = div_if_exact_i8(cj, cl);
                if y == 0i8 {
                    if cl == 1i8 {
                        y = safe_neg_i8(cj);
                    } else if cl == -1i8 {
                        y = cj;
                    } else {
                        y = 0i8;
                    }
                }
                val = y;
            } else {
                val = 0i8;
            }
            row.push(val);
            j = j + 1;
        }
        result.push(row);
        i = i + 1;
    }

    result
}
// </vc-code>


}
fn main() {}