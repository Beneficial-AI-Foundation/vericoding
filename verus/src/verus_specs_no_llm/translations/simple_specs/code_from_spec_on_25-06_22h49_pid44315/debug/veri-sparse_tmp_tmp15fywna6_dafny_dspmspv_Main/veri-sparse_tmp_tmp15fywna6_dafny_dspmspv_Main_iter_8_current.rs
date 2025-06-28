use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

// Helper function to find index of element in sorted array
spec fn index(x: nat, arr: Vec<nat>) -> nat
    decreases arr.len()
    ensures
        index(x, arr) <= arr.len(),
        index(x, arr) < arr.len() ==> arr[index(x, arr) as int] == x
{
    if arr.len() == 0 {
        0
    } else if arr[0] == x {
        0
    } else {
        let sub_arr = arr.subrange(1, arr.len() as int);
        let sub_index = index(x, sub_arr);
        if sub_index < sub_arr.len() {
            1 + sub_index
        } else {
            arr.len()
        }
    }
}

// Helper lemma to prove index properties
proof fn lemma_index_properties(x: nat, arr: Vec<nat>)
    ensures 
        index(x, arr) <= arr.len(),
        index(x, arr) < arr.len() ==> arr[index(x, arr) as int] == x
    decreases arr.len()
{
    if arr.len() == 0 {
        // base case
    } else if arr[0] == x {
        // found case
    } else {
        let sub_arr = arr.subrange(1, arr.len() as int);
        lemma_index_properties(x, sub_arr);
    }
}

// Helper lemma for sum function bounds
proof fn lemma_sum_bounds(X_val: Vec<int>, X_crd: Vec<nat>, v_val: Vec<int>, v_crd: Vec<nat>, 
                         start_pos: nat, end_pos: nat)
    requires
        X_val.len() == X_crd.len(),
        v_val.len() == v_crd.len(),
        start_pos <= end_pos,
        end_pos <= X_crd.len(),
        start_pos <= X_crd.len()
    ensures
        start_pos <= X_crd.len(),
        end_pos <= X_crd.len(),
        0 <= v_crd.len(),
        v_val.len() <= v_crd.len()
{
}

fn notin(
    X_val: Vec<int>, 
    X_crd: Vec<nat>, 
    X_pos: Vec<nat>, 
    X_crd1: Vec<nat>, 
    X_len: nat, 
    v_val: Vec<int>, 
    v_crd: Vec<nat>
) -> (y: Vec<int>)
    requires 
        // X_pos is sorted
        forall|i: int, j: int| 0 <= i < j < X_pos.len() ==> X_pos[i] <= X_pos[j],
        // X_pos indices are valid
        forall|i: int| 0 <= i < X_pos.len() ==> 0 <= X_pos[i] <= X_val.len(),
        // X_len constraint
        X_len >= X_crd1.len(),
        // X_crd1 elements are valid indices
        forall|i: int| 0 <= i < X_crd1.len() ==> X_crd1[i] < X_len,
        // X_crd1 length constraint
        X_crd1.len() < X_pos.len(),
        // X_crd1 is sorted
        forall|i: int, j: int| 0 <= i < j < X_crd1.len() ==> X_crd1[i] < X_crd1[j],
        // v requirements
        v_val.len() == v_crd.len(),
        // Additional requirements for sum function
        X_val.len() == X_crd.len()
    ensures 
        y.len() == X_len,
        forall|i: int| 0 <= i < y.len() ==> 
            y[i] == if index(i as nat, X_crd1) < X_crd1.len() && (index(i as nat, X_crd1) as int + 1) < X_pos.len() {
                sum(X_val, X_crd, v_val, v_crd, X_pos[index(i as nat, X_crd1) as int], 0, X_pos[index(i as nat, X_crd1) as int + 1], v_val.len())
            } else {
                0
            }
{
    let mut y = Vec::new();
    let mut i: nat = 0;
    
    while i < X_len
        invariant 
            i <= X_len,
            y.len() == i,
            forall|k: int| 0 <= k < i ==> 
                y[k] == if index(k as nat, X_crd1) < X_crd1.len() && (index(k as nat, X_crd1) as int + 1) < X_pos.len() {
                    sum(X_val, X_crd, v_val, v_crd, X_pos[index(k as nat, X_crd1) as int], 0, X_pos[index(k as nat, X_crd1) as int + 1], v_val.len())
                } else {
                    0
                }
    {
        proof {
            lemma_index_properties(i, X_crd1);
        }
        
        let idx = index(i, X_crd1);
        let val = if idx < X_crd1.len() {
            proof {
                assert(idx < X_crd1.len());
                assert(idx as int < X_crd1.len());
                assert(X_crd1[idx as int] < X_len);
                assert(X_crd1.len() < X_pos.len());
                assert(idx as int < X_pos.len());
                if (idx as int + 1) < X_pos.len() {
                    assert((idx as int + 1) < X_pos.len());
                }
            }
            if (idx as int + 1) < X_pos.len() {
                let start_pos = X_pos[idx as int];
                let end_pos = X_pos[idx as int + 1];
                proof {
                    // Prove bounds for sum function
                    assert(idx as int < X_pos.len());
                    assert((idx as int + 1) < X_pos.len());
                    assert(start_pos <= end_pos); // from X_pos being sorted
                    assert(end_pos <= X_val.len()); // from X_pos constraint
                    assert(start_pos <= X_val.len()); // from X_pos constraint
                    assert(start_pos <= X_crd.len()); // from X_val.len() == X_crd.len()
                    assert(end_pos <= X_crd.len()); // from X_val.len() == X_crd.len()
                    lemma_sum_bounds(X_val, X_crd, v_val, v_crd, start_pos, end_pos);
                }
                sum(X_val, X_crd, v_val, v_crd, start_pos, 0, end_pos, v_val.len())
            } else {
                0
            }
        } else {
            0
        };
        y.push(val);
        i = i + 1;
    }
    
    y
}

// ATOM
spec fn sum(X_val: Vec<int>, X_crd: Vec<nat>, v_val: Vec<int>, v_crd: Vec<nat>, kX: nat, kV: nat, pX_end: nat, pV_end: nat) -> int
    requires 
        X_val.len() == X_crd.len(),
        pX_end <= X_crd.len(),
        kX <= pX_end,
        v_val.len() == v_crd.len(),
        pV_end <= v_crd.len(),
        kV <= pV_end
    decreases pX_end + pV_end - kX - kV
{
    if pV_end <= kV || pX_end <= kX {
        0
    } else if kX < X_crd.len() && kV < v_crd.len() && kX < pX_end && kV < pV_end && X_crd[kX as int] == v_crd[kV as int] {
        sum(X_val, X_crd, v_val, v_crd, kX + 1, kV + 1, pX_end, pV_end) + v_val[kV as int] * X_val[kX as int]
    } else if kX < X_crd.len() && kV < v_crd.len() && kX < pX_end && kV < pV_end && X_crd[kX as int] < v_crd[kV as int] {
        sum(X_val, X_crd, v_val, v_crd, kX + 1, kV, pX_end, pV_end)
    } else if kX < X_crd.len() && kV < v_crd.len() && kX < pX_end && kV < pV_end {
        sum(X_val, X_crd, v_val, v_crd, kX, kV + 1, pX_end, pV_end)
    } else {
        0
    }
}

// ATOM
spec fn index_seq(x: nat, y: Seq<nat>) -> nat
    decreases y.len()
    ensures 
        index_seq(x, y) <= y.len(),
        index_seq(x, y) < y.len() ==> y[index_seq(x, y) as int] == x
{
    if y.len() == 0 {
        0
    } else if y[0] == x {
        0
    } else {
        let sub_seq = y.subrange(1, y.len());
        let sub_index = index_seq(x, sub_seq);
        if sub_index < sub_seq.len() {
            1 + sub_index
        } else {
            y.len()
        }
    }
}

// ATOM
spec fn min(x: nat, y: nat) -> nat {
    if x <= y { x } else { y }
}

// ATOM
spec fn notin_seq(y: nat, x: Seq<nat>) -> bool {
    forall|i: int| 0 <= i < x.len() ==> y != x[i]
}

}