use vstd::prelude::*;

verus! {

spec fn sum(X_val: Seq<int>, X_crd: Seq<nat>, v: Seq<int>, b: int, k: int) -> int
    decreases k - b
{
    if k <= b {
        0
    } else {
        sum(X_val, X_crd, v, b + 1, k) + X_val[b] * v[X_crd[b] as int]
    }
}

// <vc-helpers>
spec fn sum_lemma_base(X_val: Seq<int>, X_crd: Seq<nat>, v: Seq<int>, b: int)
    requires b >= 0
    ensures sum(X_val, X_crd, v, b, b) == 0
{
}

proof fn sum_loop_invariant_helper(X_val: Seq<int>, X_crd: Seq<nat>, v: Seq<int>, start: int, current: int, end: int, acc: int)
    requires 
        start <= current <= end,
        forall|i: int| start <= i < current ==> 0 <= X_crd[i] < v.len(),
        acc == sum(X_val, X_crd, v, start, current)
    ensures
        current < end ==> sum(X_val, X_crd, v, start, current + 1) == acc + X_val[current] * v[X_crd[current] as int]
{
    if current < end {
        assert(sum(X_val, X_crd, v, start, current + 1) == sum(X_val, X_crd, v, start + 1, current + 1) + X_val[start] * v[X_crd[start] as int]);
        sum_shift_lemma(X_val, X_crd, v, start, current + 1);
    }
}

proof fn sum_shift_lemma(X_val: Seq<int>, X_crd: Seq<nat>, v: Seq<int>, start: int, end: int)
    requires start < end
    ensures sum(X_val, X_crd, v, start, end) == sum(X_val, X_crd, v, start + 1, end) + X_val[start] * v[X_crd[start] as int]
    decreases end - start
{
    if end <= start + 1 {
        assert(sum(X_val, X_crd, v, start + 1, end) == 0);
    } else {
        sum_shift_lemma(X_val, X_crd, v, start + 1, end);
    }
}
// </vc-helpers>

// <vc-spec>
fn SpMV(X_val: &[int], X_crd: &[nat], X_pos: &[nat], v: &[int]) -> (y: Vec<int>)
    requires 
        X_crd.len() >= 1,
        X_crd.len() == X_val.len(),
        forall|i: int, j: int| 0 <= i < j < X_pos.len() ==> X_pos[i] <= X_pos[j],
        forall|i: int| 0 <= i < X_crd.len() ==> X_crd[i] < v.len(),
        forall|i: int| 0 <= i < X_pos.len() ==> X_pos[i] <= X_val.len(),
        X_pos.len() >= 1,
    ensures
        y.len() + 1 == X_pos.len(),
        forall|i: int| 0 <= i < y.len() ==> y[i] == sum(X_val@, X_crd@, v@, X_pos[i] as int, X_pos[i + 1] as int),
// </vc-spec>
// <vc-code>
{
    let mut y = Vec::new();
    
    for i in 0..(X_pos.len() - 1)
        invariant
            y.len() == i,
            forall|j: int| 0 <= j < i ==> y[j] == sum(X_val@, X_crd@, v@, X_pos[j] as int, X_pos[j + 1] as int),
    {
        let start = X_pos[i] as usize;
        let end = X_pos[i + 1] as usize;
        let mut acc: int = 0int;
        
        for j in start..end
            invariant
                start <= j <= end,
                acc == sum(X_val@, X_crd@, v@, start as int, j as int),
                forall|k: int| start <= k < j ==> 0 <= X_crd[k] < v@.len(),
        {
            proof {
                sum_loop_invariant_helper(X_val@, X_crd@, v@, start as int, j as int, end as int, acc);
            }
            acc = acc + X_val[j] * v[X_crd[j] as usize];
        }
        
        proof {
            assert(acc == sum(X_val@, X_crd@, v@, start as int, end as int));
            assert(sum(X_val@, X_crd@, v@, X_pos[i] as int, X_pos[i + 1] as int) == acc);
        }
        
        y.push(acc);
    }
    
    y
}
// </vc-code>

// 0 0 0 0 0 0 1 0
// 0 0 0 0 0 0 0 0
// 0 0 0 0 1 0 0 0
// 0 0 0 0 0 0 0 0
// 0 0 1 0 0 0 0 0
// 0 0 0 0 0 0 0 0
// 1 0 0 0 0 0 0 0
// 0 0 0 0 0 0 0 0

fn main() {
}

}