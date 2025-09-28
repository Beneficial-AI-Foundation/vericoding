// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): pointwise index equality from sequence equality */
proof fn seq_index_eq_implied<T>(s1: Seq<T>, s2: Seq<T>, i: int)
    requires
        s1 == s2,
        0 <= i < s1.len() as int,
    ensures
        s1[i] == s2[i],
{
}

/* helper modified by LLM (iteration 5): pushing preserves previous indices */
proof fn seq_push_index_preserve<T>(s: Seq<T>, v: T, j: int)
    requires
        0 <= j < s.len() as int,
    ensures
        s.push(v)[j] == s[j],
{
}

/* helper modified by LLM (iteration 5): value at the new last index after push */
proof fn seq_push_index_last<T>(s: Seq<T>, v: T)
    ensures
        s.push(v)[s.len() as int] == v,
{
}
// </vc-helpers>

// <vc-spec>
fn equal(x1: Vec<String>, x2: Vec<String>) -> (result: Vec<bool>)
    requires x1.len() == x2.len(),
    ensures
        result.len() == x1.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i as int] == (x1[i as int] == x2[i as int]),
        forall|i: int| 0 <= i < result.len() ==> (result[i as int] == true <==> x1[i as int] == x2[i as int]),
        x1@ == x2@ ==> forall|i: int| 0 <= i < result.len() ==> result[i as int] == true,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): corrected bound assertions using n to avoid Vec len in proof context */
    let n = x1.len();
    let mut res: Vec<bool> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            x1.len() == n,
            x2.len() == n,
            i as int <= n as int,
            res.len() == i,
            forall|j: int| 0 <= j < i as int ==> res@[j] == (x1@[j] == x2@[j]),
        decreases n as int - i as int
    {
        let old_i = i;
        let old_res = res@;
        proof {
            assert(old_res == res@);
            assert((old_res.len() as int) == old_i as int);
            assert forall|j: int| 0 <= j < old_i as int implies old_res[j] == (x1@[j] == x2@[j]) by {
                assert(old_res == res@);
            };
        }

        let b = x1[i] == x2[i];
        res.push(b);

        proof {
            assert(res@ == old_res.push(b));

            assert forall|j: int| 0 <= j < old_i as int implies res@[j] == (x1@[j] == x2@[j]) by {
                assert(res@ == old_res.push(b));
                assert((old_res.len() as int) == old_i as int);
                assert(j < old_res.len() as int);
                assert((old_res.push(b))[j] == old_res[j]);
                assert(old_res[j] == (x1@[j] == x2@[j]));
            };

            assert((old_res.len() as int) == old_i as int);
            assert((old_res.push(b))[old_res.len() as int] == b);
            assert(res@[old_i as int] == (old_res.push(b))[old_res.len() as int]);

            assert(0 <= old_i as int && old_i as int < n as int);
            assert(x1@.len() as int == n as int);
            assert(x2@.len() as int == n as int);
            assert(b == (x1@[old_i as int] == x2@[old_i as int]));
        }

        i = old_i + 1;
    }
    res
}
// </vc-code>

}
fn main() {}