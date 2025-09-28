// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): keep simple square identities to aid reasoning about 0 and 1 */
proof fn square_identities()
    ensures
        0 * 0 == 0,
        1 * 1 == 1,
{
}

/* helper modified by LLM (iteration 5): bound the square for small nonnegative integers */
proof fn square_bounds(k: int)
    requires
        0 <= k,
        k <= 11,
    ensures
        0 <= k * k,
        k * k <= 121,
{
}

/* helper modified by LLM (iteration 5): casting roundtrip for small nonnegative ints to i8 */
proof fn cast_i8_roundtrip_nonneg(r: int)
    requires
        0 <= r,
        r <= 127,
    ensures
        ((r as i8) as int) == r,
{
}

// </vc-helpers>

// <vc-spec>
fn sqrt(x: Vec<i8>) -> (result: Vec<i8>)
    ensures 
        result@.len() == x@.len(),
        forall|i: int| 0 <= i < x@.len() ==> {
            &&& (x@[i] >= 0 ==> result@[i] * result@[i] == x@[i] && result@[i] >= 0)
            &&& (x@[i] == 0 ==> result@[i] == 0)
            &&& (x@[i] == 1 ==> result@[i] == 1)
        }
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fix invariant block expression commas and maintain simple search-based sqrt for small nonnegative values */
    let n = x.len();
    let mut res: Vec<i8> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            n == x.len(),
            res@.len() == i as int,
            forall|j: int| 0 <= j < i as int ==> (0 <= #[trigger] res@[j] && res@[j] <= 11),
            forall|j: int| 0 <= j < i as int ==> {
                &&& (x@[j] == 0 ==> res@[j] == 0)
                &&& (x@[j] == 1 ==> res@[j] == 1)
            },
        decreases (n - i) as int
    {
        assert(i < x.len());
        let xi = x[i];
        if xi == 0 {
            res.push(0i8);
        } else if xi == 1 {
            res.push(1i8);
        } else if xi >= 0 {
            let xi_i: int = xi as int;
            let mut found: bool = false;
            let mut r: int = 0;
            let mut k: int = 0;
            while k <= 11 && !found
                invariant
                    0 <= k <= 12,
                    0 <= r <= 11,
                    found ==> r * r == xi_i,
                decreases 12 - k
            {
                if k * k == xi_i {
                    r = k;
                    found = true;
                }
                k = k + 1;
            }
            if found {
                let r_i8: i8 = r as i8;
                res.push(r_i8);
            } else {
                res.push(0i8);
            }
        } else {
            res.push(0i8);
        }
        i = i + 1;
    }
    let result = res;
    result
}
// </vc-code>


}
fn main() {}