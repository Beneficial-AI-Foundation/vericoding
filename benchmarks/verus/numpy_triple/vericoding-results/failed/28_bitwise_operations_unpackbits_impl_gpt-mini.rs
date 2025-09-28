// <vc-preamble>
use vstd::prelude::*;
use vstd::arithmetic::power::pow;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): relate right-shift and division for u8 with int exponent */
fn byte_shift_div_eq(v: u8, k: int)
    requires
        0 <= k && k < 8,
    ensures
        (((v >> (k as usize)) & 1) as int) == ((v as int) / pow(2, k as nat)) % 2,
{
    proof {
        let vi: int = v as int;
        let p: int = pow(2, k as nat);
        let q: int = vi / p;
        assert(0 <= vi);
        assert(vi < 256);
        assert(0 <= q);
        assert(q <= 255);
        assert((q as u8) == (v >> (k as usize)));
        assert((((v >> (k as usize)) & 1) as int) == q % 2);
    }
}

// </vc-helpers>

// <vc-spec>
fn numpy_unpackbits(a: Vec<u8>) -> (result: Vec<u8>)
    requires forall|i: int| 0 <= i < a@.len() ==> a@[i] < 256,
    ensures 
        result@.len() == a@.len() * 8,
        forall|i: int, j: int| 0 <= i < a@.len() && 0 <= j < 8 ==> 
            #[trigger] result@[i * 8 + j] == ((a@[i] as int) / pow(2, (7 - j) as nat)) % 2
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): implement unpackbits using shifts and call corrected helper */
    let n: usize = a.len();
    let mut res: Vec<u8> = Vec::new();
    let mut i: usize = 0;
    while i < n {
        let ai: u8 = a[i];
        let mut j: usize = 0;
        while j < 8 {
            let shift: usize = 7usize - j;
            let bit: u8 = ((ai >> shift) & 1) as u8;
            res.push(bit);
            j = j + 1;
        }
        i = i + 1;
    }
    proof {
        assert(res@.len() == a@.len() * 8);
        let mut ii: int = 0;
        while ii < a@.len()
            invariant
                0 <= ii && ii <= a@.len(),
                forall|x: int, y: int| 0 <= x < ii && 0 <= y < 8 ==> res@[x * 8 + y] == ((a@[x] as int) / pow(2, (7 - y) as nat)) % 2,
            decreases a@.len() - ii
        {
            let mut jj: int = 0;
            while jj < 8
                invariant
                    0 <= jj && jj <= 8,
                    forall|y: int| 0 <= y < jj ==> res@[ii * 8 + y] == ((a@[ii] as int) / pow(2, (7 - y) as nat)) % 2,
                decreases 8 - jj
            {
                byte_shift_div_eq(a@[ii], 7 - jj);
                assert(res@[ii * 8 + jj] == ((a@[ii] as int) / pow(2, (7 - jj) as nat)) % 2);
                jj = jj + 1;
            }
            ii = ii + 1;
        }
    }
    res
}

// </vc-code>

}
fn main() {}