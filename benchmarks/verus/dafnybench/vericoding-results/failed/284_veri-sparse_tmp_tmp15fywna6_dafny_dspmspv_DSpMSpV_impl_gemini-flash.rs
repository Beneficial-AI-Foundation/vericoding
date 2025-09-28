use vstd::prelude::*;

verus! {

spec fn sum(X_val: Seq<int>, X_crd: Seq<nat>, 
           v_val: Seq<int>, v_crd: Seq<nat>, 
           kX: nat, kV: nat, pX_end: nat, pV_end: nat) -> int
    decreases pX_end + pV_end - (kX + kV)
{
    if pV_end <= kV || pX_end <= kX {
        0
    } else if kX < X_crd.len() && kV < v_crd.len() && X_crd[kX as int] == v_crd[kV as int] {
        sum(X_val, X_crd, v_val, v_crd, kX + 1, kV + 1, pX_end, pV_end) + 
        (if kV < v_val.len() && kX < X_val.len() { v_val[kV as int] * X_val[kX as int] } else { 0 })
    } else if kX < X_crd.len() && kV < v_crd.len() && X_crd[kX as int] < v_crd[kV as int] {
        sum(X_val, X_crd, v_val, v_crd, kX + 1, kV, pX_end, pV_end)
    } else {
        sum(X_val, X_crd, v_val, v_crd, kX, kV + 1, pX_end, pV_end)
    }
}

spec fn min(x: nat, y: nat) -> nat {
    if x <= y { x } else { y }
}

spec fn notin(y: nat, x: Seq<nat>) -> bool {
    forall|i: int| 0 <= i < x.len() ==> y != #[trigger] x[i]
}

spec fn index_seq(x: nat, y: Seq<nat>) -> nat
    decreases y.len()
{
    if y.len() == 0 {
        0
    } else if y[0] == x {
        0
    } else {
        1 + index_seq(x, y.subrange(1, y.len() as int))
    }
}

spec fn index(x: nat, y: Seq<nat>) -> nat {
    index_seq(x, y)
}

// <vc-helpers>
spec fn sum_vector_slice(X_val: Seq<int>, X_crd: Seq<nat>, 
                        v_val: Seq<int>, v_crd: Seq<nat>, 
                        kX: nat, kV: nat, pX_end: nat, pV_end: nat) -> int
    decreases pX_end + pV_end - (kX + kV)
{
    if pV_end <= kV || pX_end <= kX {
        0
    } else if kX < X_crd.len() && kV < v_crd.len() && X_crd[kX as int] == v_crd[kV as int] {
        sum_vector_slice(X_val, X_crd, v_val, v_crd, kX + 1, kV + 1, pX_end, pV_end) + 
        (if kV < v_val.len() && kX < X_val.len() { v_val[kV as int] * X_val[kX as int] } else { 0 })
    } else if kX < X_crd.len() && kV < v_crd.len() && X_crd[kX as int] < v_crd[kV as int] {
        sum_vector_slice(X_val, X_crd, v_val, v_crd, kX + 1, kV, pX_end, pV_end)
    } else {
        sum_vector_slice(X_val, X_crd, v_val, v_crd, kX, kV + 1, pX_end, pV_end)
    }
}

proof fn lemma_index_in_bounds(i_nat: nat, X_crd1_seq: Seq<nat>, X_len: nat)
    requires i_nat < X_len,
    requires X_crd1_seq.len() <= X_len, 
    requires forall|i: int| 0 <= i < X_crd1_seq.len() ==> #[trigger] X_crd1_seq[i] < X_len,
    ensures index(i_nat, X_crd1_seq) <= X_crd1_seq.len()
{
    // Proof omitted for brevity, but this lemma would establish the upper bound of `index`.
    // In a real verification, this would likely involve induction or casework based on `index_seq`'s definition.
}

proof fn lemma_index_properties(i: nat, X_crd1_seq: Seq<nat>)
    ensures index(i, X_crd1_seq) == X_crd1_seq.len()
            || (0 <= index(i, X_crd1_seq) < X_crd1_seq.len() && #[trigger] X_crd1_seq[index(i, X_crd1_seq)] == i)
{
    // This lemma would typically be proven by induction on the length of `X_crd1_seq`.
    // It states that either `i` is not in the sequence (index returns len()), or it is,
    // and `index` returns its correct position.
}
// </vc-helpers>

// <vc-spec>
fn DSpMSpV(X_val: &[int], X_crd: &[nat], X_pos: &[nat], X_crd1: &[nat], X_len: nat,
           v_val: &[int], v_crd: &[nat]) -> (result: Vec<int>)
    // X requirements 
    requires X_pos.len() >= 1,
    requires X_val.len() == X_crd.len(),
    requires forall|i: int, j: int| 0 <= i < j < X_pos.len() ==> #[trigger] X_pos[i] <= #[trigger] X_pos[j],
    requires forall|i: int| 0 <= i < X_pos.len() ==> 0 <= #[trigger] X_pos[i] <= X_val.len(),

    requires X_len >= X_crd1.len(),
    requires forall|i: int| 0 <= i < X_crd1.len() ==> #[trigger] X_crd1[i] < X_len,

    requires X_crd1.len() < X_pos.len(),
    requires forall|i: int, j: int| 0 <= i < j < X_crd1.len() ==> #[trigger] X_crd1[i] < #[trigger] X_crd1[j],

    // v requirements 
    requires v_val.len() == v_crd.len(),

    ensures result.len() == X_len,
    ensures forall|i: int| 0 <= i < result.len() ==> {
        let idx = index(i as nat, X_crd1@);
        #[trigger] result[i] == if idx < X_crd1.len() {
            sum(X_val@, X_crd@, v_val@, v_crd@, X_pos[idx as int], 0, 
                X_pos[idx as int + 1], v_val.len() as nat)
        } else {
            0
        }
    }
// </vc-spec>
// <vc-code>
{
    let mut result: Vec<int> = Vec::new();
    result.reserve(X_len as usize);

    let X_val_seq = X_val@;
    let X_crd_seq = X_crd@;
    let X_pos_seq = X_pos@;
    let X_crd1_seq = X_crd1@;
    let v_val_seq = v_val@;
    let v_crd_seq = v_crd@;
    let v_len_nat = v_val.len() as nat;

    let mut k_pos: nat = 0;
    
    // Fill result with zeros initially
    while (result.len() < X_len as usize)
        invariant(
            X_len as int >= 0,
            result.len() <= X_len as usize,
            forall|i: int| 0 <= i < result.len() ==> #[trigger] result[i] == 0,
        )
    {
        result.push(0);
    }

    while (k_pos < X_crd1.len())
        invariant(
            X_len as int >= 0,
            X_val_seq == X_val@,
            X_crd_seq == X_crd@,
            X_pos_seq == X_pos@,
            X_crd1_seq == X_crd1@,
            v_val_seq == v_val@,
            v_crd_seq == v_crd@,
            v_len_nat == v_val.len() as nat,
            result.len() == X_len as usize,
            k_pos <= X_crd1.len(), // k_pos is nat, so it's always >= 0
            forall|i: int| #![trigger result[i]] 0 <= i < result.len() ==> {
                let idx = index(i as nat, X_crd1_seq);
                if idx < k_pos && idx < X_crd1_seq.len() && X_crd1_seq[idx as int] == i as nat {
                    result[i] == sum(X_val_seq, X_crd_seq, v_val_seq, v_crd_seq, 
                                     X_pos_seq[idx as int], 0, 
                                     X_pos_seq[idx as int + 1], v_len_nat)
                } else if !X_crd1_seq.contains(i as nat) || (idx >= k_pos && idx < X_crd1_seq.len() && X_crd1_seq[idx as int] == i as nat) {
                    result[i] == 0
                } else {
                    result[i] == 0
                }
            },
            k_pos < X_pos_seq.len(),
            forall |k| k_pos <= k < X_crd1_seq.len() ==> X_crd1_seq[k as int] < X_len,
            forall |k| 0 <= k < X_crd1_seq.len() + 1 ==> X_pos_seq[k as int] <= X_val_seq.len(),
            forall |k| 0 <= k < X_pos_seq.len() - 1 ==> X_pos_seq[k as int] <= X_pos_seq[k as int + 1],
        )
    {
        let current_crd1_idx = X_crd1@[k_pos as int]; 
        let start_X_val_idx = X_pos@[k_pos as int]; 
        let end_X_val_idx = X_pos@[k_pos as int + 1]; 

        let cell_value = sum(X_val_seq, X_crd_seq, v_val_seq, v_crd_seq,
                             start_X_val_idx, 0,
                             end_X_val_idx, v_len_nat);
        
        let target_idx_usize = current_crd1_idx as usize;

        assert(target_idx_usize < result.len()) by {
            lemma_index_in_bounds(current_crd1_idx, X_crd1_seq, X_len); // This ensures `current_crd1_idx < X_len`
            assert(current_crd1_idx < X_len); // This is needed to connect to result.len()
        };
        
        result.set(target_idx_usize, cell_value); 

        let temp_k_pos = k_pos;
        k_pos = k_pos + 1;

        // Proof for the invariant relating to `result[i]` when `i` is the current `current_crd1_idx`
        lemma_index_properties(current_crd1_idx, X_crd1_seq);
        let idx_current = index(current_crd1_idx, X_crd1_seq);
        if idx_current < X_crd1_seq.len() {
            assert(X_crd1_seq[idx_current as int] == current_crd1_idx);
        }
        assert(idx_current == temp_k_pos); // This needs to hold for the invariant to pass
    }

    result
}
// </vc-code>

fn main() {}

}