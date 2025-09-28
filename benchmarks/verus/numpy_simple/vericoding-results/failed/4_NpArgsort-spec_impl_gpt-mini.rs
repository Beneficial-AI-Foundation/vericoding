// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): find index of minimal a[res[*]] in suffix starting at start */
fn find_min_index(res: &Vec<usize>, a: &Vec<i8>, start: usize) -> (result: usize)
    requires
        start < res.len(),
    ensures
        start <= result && result < res.len(),
        forall|j: int| start as int <= j < res.len() as int ==> a@[res@[result as int] as int] <= a@[res@[j as int] as int],
{
    let n = res.len();
    let mut cur: usize = start;
    let mut j: usize = start + 1;
    while j < n
        invariant
            start <= cur && cur < n,
            start <= j && j <= n,
            forall|t: int| start as int <= t < j as int ==> a@[res@[cur as int] as int] <= a@[res@[t as int] as int],
        decreases n - j
    {
        if a[res[j]] < a[res[cur]] {
            cur = j;
        }
        j = j + 1;
    }
    cur
}
// </vc-helpers>

// <vc-spec>
fn argsort(a: Vec<i8>) -> (result: Vec<usize>)
    ensures 
        result.len() == a.len(),
        forall|i: int, j: int| 0 <= i < j < result.len() ==> #[trigger] a@[result@[i] as int] <= #[trigger] a@[result@[j] as int],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): selection sort on indices returning sorted index vector, manual swap to avoid &mut param issue */
    let n = a.len();

    let mut res: Vec<usize> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            res.len() == i,
            i <= n,
        decreases n - i
    {
        res.push(i);
        i = i + 1;
    }

    let mut i: usize = 0;
    while i < n
        invariant
            forall|p: int, q: int| 0 <= p < q < (i as int) ==> a@[res@[p as int] as int] <= a@[res@[q as int] as int],
            forall|p: int, q: int| 0 <= p < (i as int) <= q < (n as int) ==> a@[res@[p as int] as int] <= a@[res@[q as int] as int],
            res.len() == n,
        decreases n - i
    {
        let k = find_min_index(&res, &a, i);
        proof {
            assert(k < res.len());
        }
        // manual swap to avoid &mut borrow on complex expression
        let tmp: usize = res[k];
        res[k] = res[i];
        res[i] = tmp;
        i = i + 1;
    }

    res
}
// </vc-code>


}
fn main() {}