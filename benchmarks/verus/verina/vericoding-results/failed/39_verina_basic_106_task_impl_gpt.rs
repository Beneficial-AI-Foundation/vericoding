// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): transitivity lemma: from 0 <= j, j < i, and i <= n, conclude j < n */
proof fn lemma_lt_trans(j: int, i: int, n: int)
    requires
        0 <= j,
        j < i,
        i <= n,
    ensures
        j < n,
{
    assert(j < n);
}

// </vc-helpers>

// <vc-spec>
fn array_sum(a: &Vec<i32>, b: &Vec<i32>) -> (result: Vec<i32>)
    requires a.len() == b.len(),
    ensures
        result.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> result[i] == a[i] + b[i],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): implement element-wise sum with loop and quantified invariant; fix assert_forall_by syntax */
    let n = a.len();
    let mut res: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            a.len() == n,
            b.len() == n,
            i <= n,
            res.len() == i,
            forall|j: int| 0 <= j, j < i as int ==> res@[j] == a[j] + b[j],
        decreases n - i
    {
        let ai = a[i];
        let bi = b[i];
        let sum = ai + bi;
        let ghost old_res = res@;
        res.push(sum);
        proof {
            assert(res@ == old_res.push(sum));
            assert_forall_by(|j: int|
                requires 0 <= j, j < (i + 1) as int
                ensures res@[j] == a[j] + b[j],
            {
                if j < i as int {
                    assert((old_res.push(sum))[j] == old_res[j]);
                    assert(res@[j] == old_res[j]);
                } else {
                    assert(j == i as int);
                    assert((old_res.push(sum))[old_res.len()] == sum);
                    assert(res@[j] == sum);
                    assert(a[j] == a[i as int]);
                    assert(b[j] == b[i as int]);
                    assert(a[i as int] == a[i]);
                    assert(b[i as int] == b[i]);
                    assert(a[j] + b[j] == a[i] + b[i]);
                }
            });
        }
        i = i + 1;
    }
    res
}
// </vc-code>

}
fn main() {}