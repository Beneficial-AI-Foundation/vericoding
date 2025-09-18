// <vc-preamble>
use vstd::prelude::*;
use vstd::arithmetic::power::pow;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): lemma to show modulo by 2 yields 0 or 1 */
proof fn lemma_mod2_range(x: int)
    ensures 0 <= x % 2 < 2
{
    assert(2 > 0);
    assert(0 <= x % 2);
    assert(x % 2 < 2);
}
// </vc-helpers>

// <vc-spec>
fn numpy_unpackbits(a: Vec<u8>) -> (result: Vec<u8>)
    requires forall|i: int| 0 <= i < a.len() ==> a[i] < 256,
    ensures 
        result.len() == a.len() * 8,
        forall|i: int, j: int| 0 <= i < a.len() && 0 <= j < 8 ==> 
            #[trigger] result[i * 8 + j] == ((a[i] as int) / pow(2, (7 - j) as nat)) % 2
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): implement unpackbits with verified nested loops and fix while-invariant syntax (no semicolons) */
    let n_usize: usize = a.len();
    let n: int = n_usize as int;
    let mut out: Vec<u8> = Vec::new();
    let mut i: int = 0;
    while i < n
        invariant 0 <= i && i <= n
        invariant out.len() as int == i * 8
        invariant forall|ii: int, jj: int|
            0 <= ii && ii < i && 0 <= jj && jj < 8 ==>
                out@[ii * 8 + jj] == ((a[ii] as int) / pow(2, (7 - jj) as nat)) % 2
        decreases n - i
    {
        assert(0 <= i && i < n);
        assert((i as nat) < (n as nat));
        assert((n as nat) == n_usize);
        let iu: usize = i as usize;
        assert(iu < n_usize);

        let ai: u8 = a[iu];
        let ai_int: int = ai as int;

        let mut j: int = 0;
        while j < 8
            invariant 0 <= j && j <= 8
            invariant out.len() as int == i * 8 + j
            invariant forall|jj: int|
                0 <= jj && jj < j ==> out@[i * 8 + jj] == (ai_int / pow(2, (7 - jj) as nat)) % 2
            invariant forall|ii: int, jj: int|
                0 <= ii && ii < i && 0 <= jj && jj < 8 ==>
                    out@[ii * 8 + jj] == ((a[ii] as int) / pow(2, (7 - jj) as nat)) % 2
            decreases 8 - j
        {
            assert(j <= 7);
            assert(0 <= 7 - j);
            let e: nat = (7 - j) as nat;
            let divisor: int = pow(2, e);
            let x: int = ai_int / divisor;
            lemma_mod2_range(x);
            let b_int: int = x % 2;
            assert(0 <= b_int && b_int < 256);
            let b: u8 = b_int as u8;
            let old_len: usize = out.len();
            out.push(b);
            assert(old_len as int == i * 8 + j);
            assert(out@[i * 8 + j] == b);
            j += 1;
        }
        i += 1;
    }
    assert(out.len() as int == n * 8);
    out
}
// </vc-code>

}
fn main() {}