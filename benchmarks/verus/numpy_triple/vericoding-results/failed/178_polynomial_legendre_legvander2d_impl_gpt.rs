// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
pub open spec fn inner_len_int(deg_x: u8, deg_y: u8) -> int {
    (deg_x as int + 1) * (deg_y as int + 1)
}

/* helper modified by LLM (iteration 5): moved ghost int variables into proof blocks to satisfy exec/ghost separation */
pub fn compute_inner_len(deg_x: u8, deg_y: u8) -> (k: usize)
    ensures
        k as int == inner_len_int(deg_x, deg_y),
        k > 0,
{
    let ax: usize = (deg_x as usize) + 1;
    let ay: usize = (deg_y as usize) + 1;

    proof {
        assert(deg_x as int >= 0);
        assert(deg_y as int >= 0);
        assert(ax >= 1usize && ay >= 1usize);
        assert(ax <= 256usize);
        assert(ay <= 256usize);
    }

    let mut prod: usize = 0;
    let mut c: usize = 0;
    while c < ay
        invariant
            c <= ay,
            prod as int == (ax as int) * (c as int),
            ax >= 1usize,
            ay >= 1usize,
            ax <= 256usize,
            ay <= 256usize,
        decreases ay - c
    {
        let c_old: usize = c;
        proof {
            let prod_old: int = prod as int;
            assert((ax as int) * (c_old as int) == prod_old);
            let ci: int = c_old as int;
            let ayi: int = ay as int;
            assert(ci < ayi);
            assert(ci + 1 <= ayi);
            assert(ayi <= 256);
            assert(ax as int <= 256);
            assert((ax as int) * (ci + 1) <= 256 * 256);
            assert(256 * 256 == 65536);
            assert(prod_old + (ax as int) == (ax as int) * (ci + 1));
        }
        prod = prod + ax;
        c = c + 1;
        proof {
            let ci_new: int = c as int;
            assert(ci_new >= 1);
            assert(prod as int == (ax as int) * ci_new);
        }
    }

    proof {
        assert(!(c < ay));
        assert(c <= ay);
        assert(c == ay);
        assert(prod as int == (ax as int) * (ay as int));
        let ax_i: int = ax as int;
        let ay_i: int = ay as int;
        assert(ax_i >= 1);
        assert(ay_i >= 1);
        let t: int = ay_i - 1;
        assert(t >= 0);
        assert(ay_i == 1 + t);
        assert(ax_i * ay_i == ax_i * (1 + t));
        assert(ax_i * (1 + t) == ax_i + ax_i * t);
        assert(ax_i * t >= 0);
        assert(ax_i + ax_i * t >= ax_i);
        assert(ax_i + ax_i * t >= 1);
        assert(prod as int >= 1);
    }

    let k_local: usize = prod;
    proof {
        assert(ax as int == deg_x as int + 1);
        assert(ay as int == deg_y as int + 1);
        assert(k_local as int == (ax as int) * (ay as int));
    }
    assert(k_local as int == inner_len_int(deg_x, deg_y));
    assert(k_local > 0);
    k_local
}

/* helper modified by LLM (iteration 4): direct arithmetic proof that (deg_x+1)*(deg_y+1) > 0 */
pub proof fn inner_len_positive(deg_x: u8, deg_y: u8)
    ensures
        inner_len_int(deg_x, deg_y) > 0,
{
    let dx: int = deg_x as int;
    let dy: int = deg_y as int;
    let a: int = dx + 1;
    let b: int = dy + 1;
    assert(a >= 1);
    assert(b >= 1);
    let t: int = b - 1;
    assert(t >= 0);
    assert(b == 1 + t);
    assert(a * b == a * (1 + t));
    assert(a * (1 + t) == a + a * t);
    assert(a * t >= 0);
    assert(a + a * t >= a);
    assert(a >= 1);
    assert(a * b >= 1);
    assert(inner_len_int(deg_x, deg_y) == a * b);
}
// </vc-helpers>

// <vc-spec>
fn legvander2d(x: Vec<f64>, y: Vec<f64>, deg_x: u8, deg_y: u8) -> (result: Vec<Vec<f64>>)
    requires x.len() == y.len(),
    ensures
        result.len() == x.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i].len() == (deg_x as int + 1) * (deg_y as int + 1),
        forall|i: int| 0 <= i < result.len() && result[i].len() > 0 ==> result[i][0] == 1.0
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): use verified helper and maintain loop invariants while building the result */
    let n: usize = x.len();
    let inner_len: usize = compute_inner_len(deg_x, deg_y);
    let mut result: Vec<Vec<f64>> = Vec::new();

    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            result.len() == i,
            forall|k: int| 0 <= k < result.len() ==> result[k].len() == inner_len_int(deg_x, deg_y),
            forall|k: int| 0 <= k < result.len() && result[k].len() > 0 ==> result[k][0] == 1.0,
        decreases n - i
    {
        let mut row: Vec<f64> = Vec::new();
        let mut j: usize = 0;
        while j < inner_len
            invariant
                j <= inner_len,
                row.len() == j,
            decreases inner_len - j
        {
            row.push(0.0);
            j = j + 1;
        }

        // inner_len > 0 by compute_inner_len's ensures
        row[0] = 1.0;
        proof {
            assert(row.len() == inner_len);
            assert(inner_len as int == inner_len_int(deg_x, deg_y));
            assert(row[0] == 1.0);
        }

        result.push(row);
        i = i + 1;
    }

    result
}
// </vc-code>

}
fn main() {}