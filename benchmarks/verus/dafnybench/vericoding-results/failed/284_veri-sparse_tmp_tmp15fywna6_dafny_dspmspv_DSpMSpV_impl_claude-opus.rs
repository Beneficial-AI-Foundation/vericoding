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
proof fn lemma_index_bounds(i: nat, crd1: Seq<nat>)
    requires 
        forall|j: int, k: int| 0 <= j < k < crd1.len() ==> #[trigger] crd1[j] < #[trigger] crd1[k],
    ensures 
        index(i, crd1) <= crd1.len(),
        forall|j: int| 0 <= j < crd1.len() && crd1[j] == i ==> index(i, crd1) == j,
        forall|j: int| 0 <= j < crd1.len() && crd1[j] != i ==> index(i, crd1) > j,
    decreases crd1.len(),
{
    if crd1.len() == 0 {
    } else if crd1[0] == i {
    } else {
        lemma_index_bounds(i, crd1.subrange(1, crd1.len() as int));
    }
}

proof fn lemma_index_not_in(i: nat, crd1: Seq<nat>)
    requires 
        forall|j: int| 0 <= j < crd1.len() ==> crd1[j] != i,
    ensures 
        index(i, crd1) == crd1.len(),
    decreases crd1.len(),
{
    if crd1.len() == 0 {
    } else {
        assert(crd1[0] != i);
        lemma_index_not_in(i, crd1.subrange(1, crd1.len() as int));
    }
}

proof fn lemma_index_in(i: nat, crd1: Seq<nat>, pos: int)
    requires 
        0 <= pos < crd1.len(),
        crd1[pos] == i,
        forall|j: int| 0 <= j < pos ==> crd1[j] != i,
    ensures 
        index(i, crd1) == pos,
    decreases pos,
{
    if pos == 0 {
        assert(crd1[0] == i);
    } else {
        assert(crd1[0] != i);
        lemma_index_in(i, crd1.subrange(1, crd1.len() as int), pos - 1);
    }
}

proof fn lemma_sum_step(X_val: Seq<int>, X_crd: Seq<nat>, 
                        v_val: Seq<int>, v_crd: Seq<nat>,
                        kX: nat, kV: nat, pX_end: nat, pV_end: nat)
    requires 
        X_val.len() == X_crd.len(),
        v_val.len() == v_crd.len(),
        kX <= pX_end,
        kV <= pV_end,
        pX_end <= X_val.len(),
        pV_end <= v_val.len(),
    ensures
        pV_end <= kV || pX_end <= kX ==> sum(X_val, X_crd, v_val, v_crd, kX, kV, pX_end, pV_end) == 0,
        kX < pX_end && kV < pV_end && kX < X_crd.len() && kV < v_crd.len() && X_crd[kX as int] == v_crd[kV as int] ==>
            sum(X_val, X_crd, v_val, v_crd, kX, kV, pX_end, pV_end) == 
            X_val[kX as int] * v_val[kV as int] + sum(X_val, X_crd, v_val, v_crd, kX + 1, kV + 1, pX_end, pV_end),
        kX < pX_end && kV < pV_end && kX < X_crd.len() && kV < v_crd.len() && X_crd[kX as int] < v_crd[kV as int] ==>
            sum(X_val, X_crd, v_val, v_crd, kX, kV, pX_end, pV_end) == 
            sum(X_val, X_crd, v_val, v_crd, kX + 1, kV, pX_end, pV_end),
        kX < pX_end && kV < pV_end && kX < X_crd.len() && kV < v_crd.len() && X_crd[kX as int] > v_crd[kV as int] ==>
            sum(X_val, X_crd, v_val, v_crd, kX, kV, pX_end, pV_end) == 
            sum(X_val, X_crd, v_val, v_crd, kX, kV + 1, pX_end, pV_end),
    decreases pX_end + pV_end - (kX + kV),
{
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
    let mut result = Vec::new();
    let mut i: usize = 0;
    
    while i < X_len
        invariant
            i <= X_len,
            result.len() == i,
            forall|j: int| 0 <= j < i ==> {
                let idx = index(j as nat, X_crd1@);
                #[trigger] result[j] == if idx < X_crd1.len() {
                    sum(X_val@, X_crd@, v_val@, v_crd@, X_pos[idx as int], 0, 
                        X_pos[idx as int + 1], v_val.len() as nat)
                } else {
                    0
                }
            },
    {
        let idx = index(i as nat, X_crd1@);
        
        if idx < X_crd1.len() {
            proof {
                lemma_index_bounds(i as nat, X_crd1@);
                assert(X_crd1[idx as int] == i);
                assert(idx + 1 < X_pos.len());
                assert(X_pos[idx as int] <= X_pos[idx as int + 1]);
                assert(X_pos[idx as int + 1] <= X_val.len());
            }
            
            let row_start = X_pos[idx];
            let row_end = X_pos[idx + 1];
            
            let mut sum_val: int = 0;
            let mut kX: usize = row_start;
            let mut kV: usize = 0;
            
            while kX < row_end && kV < v_val.len()
                invariant
                    row_start <= kX <= row_end,
                    kX <= X_val.len(),
                    0 <= kV <= v_val.len(),
                    row_end <= X_val.len(),
                    row_end <= X_crd.len(),
                    sum_val == sum(X_val@, X_crd@, v_val@, v_crd@, row_start as nat, 0, 
                                   row_end as nat, v_val.len() as nat) -
                               sum(X_val@, X_crd@, v_val@, v_crd@, kX as nat, kV as nat, 
                                   row_end as nat, v_val.len() as nat),
            {
                proof {
                    lemma_sum_step(X_val@, X_crd@, v_val@, v_crd@, kX as nat, kV as nat, 
                                   row_end as nat, v_val.len() as nat);
                }
                
                if X_crd[kX] == v_crd[kV] {
                    sum_val = sum_val + X_val[kX] * v_val[kV];
                    kX = kX + 1;
                    kV = kV + 1;
                } else if X_crd[kX] < v_crd[kV] {
                    kX = kX + 1;
                } else {
                    kV = kV + 1;
                }
            }
            
            assert(kX >= row_end || kV >= v_val.len());
            assert(sum(X_val@, X_crd@, v_val@, v_crd@, kX as nat, kV as nat, 
                       row_end as nat, v_val.len() as nat) == 0);
            assert(sum_val == sum(X_val@, X_crd@, v_val@, v_crd@, row_start as nat, 0, 
                                  row_end as nat, v_val.len() as nat));
            result.push(sum_val);
        } else {
            result.push(0);
        }
        
        i = i + 1;
    }
    
    result
}
// </vc-code>

fn main() {}

}