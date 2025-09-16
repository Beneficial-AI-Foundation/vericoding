// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn zip_halves<T>(v: Seq<T>) -> (ret: Seq<(T, T)>) {
    v.take((v.len() / 2) as int).zip_with(v.skip(((v.len() + 1) / 2) as int).reverse())
}

spec fn diff(s: Seq<(i32, i32)>) -> (ret: int) {
    s.fold_left(
        0,
        |acc: int, x: (i32, i32)|
            if (x.0 != x.1) {
                acc + 1
            } else {
                acc
            },
    )
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed literal types in diff_step_lemma ensures clause */
proof fn diff_step_lemma(v: Seq<i32>, i: int)
    requires
        0 <= i < v.len() / 2,
    ensures
        diff(zip_halves(v).take(i + 1)) == diff(zip_halves(v).take(i)) + (if v[i] != v[v.len() - 1 - i] { 1int } else { 0int }),
{
}

proof fn diff_empty_lemma()
    ensures
        diff(Seq::<(i32, i32)>::empty()) == 0,
{
}
// </vc-helpers>

// <vc-spec>
fn smallest_change(v: Vec<i32>) -> (change: usize)

    requires
        v@.len() < usize::MAX,

    ensures
        change == diff(zip_halves(v@)),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Same implementation, fixed helper types */
    let n = v.len();
    let half = n / 2;
    
    let mut count: usize = 0;
    let mut i: usize = 0;
    
    proof {
        diff_empty_lemma();
    }
    
    while i < half
        invariant
            i <= half,
            half == n / 2,
            count <= i,
            count as int == diff(zip_halves(v@).take(i as int)),
            n == v@.len(),
        decreases half - i
    {
        let left_idx = i;
        let right_idx = n - 1 - i;
        
        if v[left_idx] != v[right_idx] {
            count = count + 1;
        }
        
        i = i + 1;
        
        proof {
            diff_step_lemma(v@, (i - 1) as int);
        }
    }
    
    count
}
// </vc-code>

}
fn main() {}