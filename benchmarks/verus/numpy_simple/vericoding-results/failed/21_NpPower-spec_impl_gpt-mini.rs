// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn int_pow(base: int, exp: nat) -> int
    decreases exp
{
    if exp == 0 {
        1
    } else {
        base * int_pow(base, (exp - 1) as nat)
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): trivial proof that int_pow(base, 0) == 1 */
proof fn int_pow_zero(base: int)
    ensures
        int_pow(base, 0) == 1,
{
    proof {
        assert(int_pow(base, 0) == 1);
    }
}

/* helper modified by LLM (iteration 5): successor property for int_pow: int_pow(base, n+1) == base * int_pow(base, n) */
proof fn int_pow_succ(base: int, n: nat)
    ensures
        int_pow(base, n + 1) == base * int_pow(base, n),
{
    proof {
        assert(int_pow(base, n + 1) == base * int_pow(base, n));
    }
}
// </vc-helpers>

// <vc-spec>
fn power(a: Vec<i8>, b: Vec<u8>) -> (result: Vec<i8>)
    requires a.len() == b.len(),
    ensures 
        result.len() == a.len(),
        forall|i: int| 0 <= i < a@.len() ==> result@[i] == int_pow(a@[i] as int, b@[i] as nat),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): compute powers per-element using usize loops and spec casts */
    let mut result: Vec<i8> = Vec::new();
    let mut i: usize = 0;
    while i < a.len()
        invariant
            i <= a.len(),
            result.len() == i,
            forall |k: int| 0 <= k < (i as int) ==> result@[k as nat] == int_pow(a@[k as nat] as int, b@[k as nat] as nat),
        decreases (a.len() as nat) - (i as nat)
    {
        let base_i: i8 = a[i];
        let exp_n: usize = b[i] as usize;
        let mut p: i64 = 1;
        let mut j: usize = 0;
        while j < exp_n
            invariant
                j <= exp_n,
                (p as int) == int_pow(base_i as int, (j as nat)),
            decreases (exp_n as nat) - (j as nat)
        {
            let old_j: usize = j;
            let old_p: i64 = p;
            p = p * (base_i as i64);
            j = j + 1;
            proof {
                assert(old_p as int == int_pow(base_i as int, (old_j as nat)));
                assert(int_pow(base_i as int, ((old_j + 1) as nat)) == base_i as int * int_pow(base_i as int, (old_j as nat)));
                assert(p as int == int_pow(base_i as int, ((old_j + 1) as nat)));
            }
        }
        result.push(p as i8);
        i = i + 1;
    }
    result
}
// </vc-code>


}
fn main() {}