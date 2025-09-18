// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): no changes, just fixing compilation error in vc-code. */
spec fn has_outer_contrib(c1: Seq<f64>, c2: Seq<f64>, p: int, i_limit: int) -> bool {
    exists|j: int, k: int|
        0 <= j < i_limit && 0 <= k < c2.len() && j + k == p &&
        c1[j] != 0.0 && c2[k] != 0.0
}

spec fn has_inner_contrib(c1: Seq<f64>, c2: Seq<f64>, p: int, i: int, j_limit: int) -> bool {
    exists|k: int|
        0 <= k < j_limit && i + k == p &&
        c1[i] != 0.0 && c2[k] != 0.0
}

proof fn has_outer_contrib_is_monotonic(c1: Seq<f64>, c2: Seq<f64>, p: int, i1: int, i2: int)
    requires 
        i1 <= i2,
        has_outer_contrib(c1, c2, p, i1)
    ensures 
        has_outer_contrib(c1, c2, p, i2)
{
    let (j, k) = choose |j: int, k: int| 
        0 <= j < i1 && 0 <= k < c2.len() && j + k == p && 
        c1[j] != 0.0 && c2[k] != 0.0;
    assert(0 <= j < i2);
}
// </vc-helpers>

// <vc-spec>
fn lagmul(c1: Vec<f64>, c2: Vec<f64>) -> (result: Vec<f64>)
    requires c1.len() > 0 && c2.len() > 0,
    ensures 
        result.len() == c1.len() + c2.len() - 1,
        forall|i: int| 0 <= i < result.len() ==> 
            (result[i] != 0.0 ==> 
                exists|j: int, k: int| 
                    0 <= j < c1.len() && 
                    0 <= k < c2.len() && 
                    j + k == i && 
                    c1[j] != 0.0 && 
                    c2[k] != 0.0)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): replaced invalid implies() function call with ==> operator. */
    let n1 = c1.len();
    let n2 = c2.len();
    let res_len = n1 + n2 - 1;

    let mut result = Vec::new();
    let mut k: usize = 0;
    while k < res_len
        invariant
            k <= res_len,
            result.len() == k,
            forall|i: int| 0 <= i < result.len() ==> result[i] == 0.0,
        decreases res_len - k
    {
        result.push(0.0);
        k = k + 1;
    }

    let mut i: usize = 0;
    while i < n1
        invariant
            0 <= i <= n1,
            c1.len() == n1,
            c2.len() == n2,
            result.len() == res_len,
            forall|p: int| 0 <= p < res_len ==> 
                (result.view()[p] != 0.0 ==> 
                    has_outer_contrib(c1.view(), c2.view(), p, i as int)),
        decreases n1 - i
    {
        let mut j: usize = 0;
        while j < n2
            invariant
                0 <= i < n1,
                0 <= j <= n2,
                c1.len() == n1,
                c2.len() == n2,
                result.len() == res_len,
                forall|p: int| 0 <= p < res_len ==>
                    (result.view()[p] != 0.0 ==>
                        (has_outer_contrib(c1.view(), c2.view(), p, i as int) ||
                         has_inner_contrib(c1.view(), c2.view(), p, i as int, j as int))),
            decreases n2 - j
        {
            let p = i + j;
            let term = c1[i] * c2[j];
            if term != 0.0 {
                let ghost old_res_p = result[p as int];
                result.set(p, result[p] + term);
                
                proof {
                    if result.view()[p as int] != 0.0 && old_res_p == 0.0 {
                        assert(c1[i as int] != 0.0 && c2[j as int] != 0.0);
                        assert(has_inner_contrib(c1.view(), c2.view(), p as int, i as int, (j + 1) as int));
                    }
                }
            } 
            j = j + 1;
        }

        proof {
            let i_next = (i + 1) as int;
            assert forall|p: int| 0 <= p < res_len implies
                (result.view()[p] != 0.0 ==> 
                    has_outer_contrib(c1.view(), c2.view(), p, i_next))
            by {
                if result.view()[p] != 0.0 {
                    let outer_ok = has_outer_contrib(c1.view(), c2.view(), p, i as int);
                    let inner_ok = has_inner_contrib(c1.view(), c2.view(), p, i as int, n2 as int);
                    assert(outer_ok || inner_ok);
                    if inner_ok {
                        let k = choose|k: int| 0 <= k < n2 && (i as int) + k == p && c1.view()[i as int] != 0.0 && c2.view()[k] != 0.0;
                        assert(has_outer_contrib(c1.view(), c2.view(), p, i_next));
                    } else {
                        assert(outer_ok);
                        has_outer_contrib_is_monotonic(c1.view(), c2.view(), p, i as int, i_next);
                        assert(has_outer_contrib(c1.view(), c2.view(), p, i_next));
                    }
                }
            };
        }

        i = i + 1;
    }

    result
}
// </vc-code>

}
fn main() {}