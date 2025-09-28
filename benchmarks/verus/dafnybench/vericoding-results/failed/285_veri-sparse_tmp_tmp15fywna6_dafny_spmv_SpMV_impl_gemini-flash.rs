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
spec fn sum_range(X_val: Seq<int>, X_crd: Seq<nat>, v: Seq<int>, b: int, k: int) -> int
    decreases k - b
{
    if k <= b {
        0
    } else {
        sum_range(X_val, X_crd, v, b + 1, k) + X_val[b] * v[X_crd[b] as int]
    }
}

proof fn lemma_sum_range_split(X_val: Seq<int>, X_crd: Seq<nat>, v: Seq<int>, b: int, k: int, m: int)
    requires
        b <= m <= k,
        // Assuming X_val, X_crd, v are large enough to contain indices b to k
        k <= X_val.len(),
        k <= X_crd.len(),
        forall |idx: int| b <= idx < k ==> (X_crd[idx] as int) < v.len(),
    ensures
        sum_range(X_val, X_crd, v, b, k) == sum_range(X_val, X_crd, v, b, m) + sum_range(X_val, X_crd, v, m, k),
    decreases k - b
{
    if k <= b {
        // Base case: k <= b
        assert(sum_range(X_val, X_crd, v, b, k) == 0);
        assert(sum_range(X_val, X_crd, v, b, m) == 0);
        assert(sum_range(X_val, X_crd, v, m, k) == 0);
    } else if m == b {
        // Base case: m == b
        assert(sum_range(X_val, X_crd, v, b, k) == sum_range(X_val, X_crd, v, m, k));
        assert(sum_range(X_val, X_crd, v, b, m) == 0);
    } else if k == m {
        // Base case: k == m
        assert(sum_range(X_val, X_crd, v, m, k) == 0);
        assert(sum_range(X_val, X_crd, v, b, k) == sum_range(X_val, X_crd, v, b, m));
    } else { // b < k
        // Non-base case. Inductive step depends on b < k.
        // It also implies b+1 <= k.
        if m > b {
            lemma_sum_range_split(X_val, X_crd, v, b + 1, k, m);
            assert(sum_range(X_val, X_crd, v, b, k) ==
                   X_val[b] * v[X_crd[b] as int] + sum_range(X_val, X_crd, v, b + 1, k));
            assert(sum_range(X_val, X_crd, v, b, m) ==
                   X_val[b] * v[X_crd[b] as int] + sum_range(X_val, X_crd, v, b + 1, m));
            assert(sum_range(X_val, X_crd, v, b, k) == sum_range(X_val,X_crd,v,b,m) + sum_range(X_val,X_crd,v,m,k));
        } else { // m == b, this case is actually handled above
            // This 'else' branch is not strictly necessary due to the `m == b` base case,
            // but including it conceptually covers `b < m` and `m == b` more distinctly
            // in the recursive step logic.
        }
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
    let mut y: Vec<int> = Vec::new();
    let x_val_seq = X_val@;
    let x_crd_seq = X_crd@;
    let v_seq = v@;

    let mut i: usize = 0;
    while i < (X_pos.len() - 1)
        invariant
            0 <= i as int,
            i < X_pos.len(),
            y.len() == i,
            X_pos.len() >= 1,
            // Ensure array accesses are valid for the `sum` function.
            // X_pos[j as usize] as int and X_pos[(j + 1) as usize] as int
            // must be valid indices for x_val_seq, x_crd_seq, and v_seq.
            forall|j: int| 0 <= j < i as int ==> {
                let start = X_pos[j as usize] as int;
                let end = X_pos[(j + 1) as usize] as int;
                &&& start <= end // Required for sum (b <= k)
                &&& end <= x_val_seq.len() // X_pos values refer to X_val indices
                &&& end <= x_crd_seq.len()
                &&& (forall|idx: int| start <= idx < end ==> (x_crd_seq[idx] as int) < v_seq.len())
                &&& y[j] == sum(x_val_seq, x_crd_seq, v_seq, start, end)
            },
    {
        let start_idx: int = X_pos[i] as int;
        let end_idx: int = X_pos[i + 1] as int;
        
        let mut current_sum: int = 0;
        let mut k: int = start_idx;

        while k < end_idx
            invariant
                start_idx <= k <= end_idx,
                current_sum == sum(x_val_seq, x_crd_seq, v_seq, start_idx, k),
                start_idx == X_pos[i] as int, // Propagate value of start_idx
                end_idx == X_pos[i + 1] as int, // Propagate value of end_idx
                x_val_seq.len() == X_val.len(),
                x_crd_seq.len() == X_crd.len(),
                v_seq.len() == v.len(),
                // Ensures for `sum` function
                k <= x_val_seq.len(),
                k <= x_crd_seq.len(),
                forall|idx: int| start_idx <= idx < k ==> (x_crd_seq[idx] as int) < v_seq.len(),
                // Verus needs explicit proof for array indices within loops.
                k >= 0,
                (k as usize) < X_val.len(), // k as usize must be valid index for X_val
                (X_crd[k as usize] as usize) < v.len(), // X_crd index as usize must be valid for v
                (X_crd[k as usize] as int) < v_seq.len(), // X_crd index as int must be valid for v_seq
            decreases end_idx - k
        {
            current_sum = current_sum + X_val[k as usize] * v[X_crd[k as usize] as usize];
            proof {
                assert(sum(x_val_seq, x_crd_seq, v_seq, start_idx, k + 1) == sum(x_val_seq, x_crd_seq, v_seq, start_idx, k) + x_val_seq[k] * v_seq[x_crd_seq[k] as int]);
                assert(current_sum == sum(x_val_seq, x_crd_seq, v_seq, start_idx, k + 1));
            }
            k = k + 1;
        }
        y.push(current_sum);
        i = i + 1;
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