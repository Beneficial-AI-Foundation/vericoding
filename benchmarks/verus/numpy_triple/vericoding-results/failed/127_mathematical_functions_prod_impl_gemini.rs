// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): completed proofs */
proof fn vec_product_distributive(s1: Seq<i32>, s2: Seq<i32>)
    ensures
        vec_product_int(s1.add(s2)) == vec_product_int(s1) * vec_product_int(s2),
    decreases s1.len()
{
    if s1.len() > 0 {
        assert(s1.add(s2).skip(1) == s1.skip(1).add(s2));
        vec_product_distributive(s1.skip(1), s2);
    }
}

/* helper modified by LLM (iteration 3): completed proofs */
proof fn vec_product_has_zero(s: Seq<i32>)
    requires
        exists|i: int| 0 <= i < s.len() && s[i] == 0,
    ensures
        vec_product_int(s) == 0,
    decreases s.len()
{
    if s[0] != 0 {
        let i = choose|i: int| 0 <= i < s.len() && s[i] == 0;
        assert(i > 0);
        assert(exists|j: int| 0 <= j < s.skip(1).len() && s.skip(1)[j] == 0 by {
            let j = i - 1;
            assert(s.skip(1)[j] == s[i]);
        });
        vec_product_has_zero(s.skip(1));
    }
}

// </vc-helpers>

// <vc-spec>
spec fn vec_product_int(a: Seq<i32>) -> int 
    decreases a.len()
{
    if a.len() == 0 {
        1
    } else {
        (a[0] as int) * vec_product_int(a.skip(1))
    }
}

fn prod(a: Vec<i8>) -> (result: i8)
    ensures 
        result as int == vec_product_int(a@.map(|i, x| x as i32)),
        a.len() == 0 ==> result == 1,
        (exists|i: int| 0 <= i < a.len() && a[i] == 0) ==> result == 0
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): fixed compilation error by using i64 */
    let mut p: i64 = 1;
    let mut i: usize = 0;

    while i < a.len()
        invariant
            0 <= i <= a.len(),
            p as int == vec_product_int(a@.subrange(0, i as int).map(|_, x| x as i32)),
        decreases a.len() - i
    {
        proof {
            let s1 = a@.subrange(0, i as int).map(|_, x| x as i32);
            let s2 = seq![(a@[i] as i32)];
            assert(a@.subrange(0, (i + 1) as int).map(|_, x| x as i32) =~= s1.add(s2));
            vec_product_distributive(s1, s2);
        }
        p = p * (a[i] as i64);
        i = i + 1;
    }

    proof {
        if exists|j: int| 0 <= j < a.len() && a[j] == 0 {
            let s = a@.map(|_, x| x as i32);
            assert(exists|k: int| 0 <= k < s.len() && s[k] == 0);
            vec_product_has_zero(s);
            assert(vec_product_int(s) == 0);
        }
    }
    
    p as i8
}

// </vc-code>


}
fn main() {}