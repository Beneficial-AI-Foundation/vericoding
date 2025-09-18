// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): swapping two elements preserves multiset */
fn swap_preserves_multiset(b: &mut Vec<i32>, i: usize, j: usize)
    requires
        i < b.len(),
        j < b.len(),
    ensures
        b@.to_multiset() == old(b)@.to_multiset(),
{
    proof {
        let olds = old(b)@;
        let news = b@;
        assert(news == olds.update(i as int, olds@[j as int]).update(j as int, olds@[i as int]));
        assert(news.to_multiset() == olds.to_multiset());
    }
}

// </vc-helpers>

// <vc-spec>
fn bubble_sort(a: &Vec<i32>) -> (result: Vec<i32>)
    ensures
        result.len() == a.len(),
        forall|i: int, j: int| 0 <= i < j < result.len() ==> result[i] <= result[j],
        a@.to_multiset() == result@.to_multiset(),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): bubble sort using Vec::from and swap lemma */
    let mut b: Vec<i32> = Vec::from(a@);
    let n: usize = b.len();
    let mut pass: usize = 0;
    while pass < n
        invariant
            pass <= n,
            b@.to_multiset() == a@.to_multiset(),
        decreases n - pass,
    {
        let mut i: usize = 0;
        while i + 1 < n - pass
            invariant
                i <= n - pass,
                b@.to_multiset() == a@.to_multiset(),
            decreases n - pass - i,
        {
            let j = i + 1;
            if b[i] > b[j] {
                let vi = b[i];
                let vj = b[j];
                b.set(i, vj);
                b.set(j, vi);
                proof {
                    swap_preserves_multiset(&mut b, i, j);
                }
            }
            i = i + 1;
        }
        pass = pass + 1;
    }
    b
}

// </vc-code>

}
fn main() {}