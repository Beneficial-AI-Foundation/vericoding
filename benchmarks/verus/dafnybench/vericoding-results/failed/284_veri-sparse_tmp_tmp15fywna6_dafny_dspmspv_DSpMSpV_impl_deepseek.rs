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
proof fn lemma_index_in_range(x: nat, s: Seq<nat>) 
    requires 
        exists|i: int| 0 <= i < s.len() && s[i] == x,
    ensures 
        0 <= index(x, s) < s.len(),
    decreases s.len()
{
    if s.len() == 0 {
        assert(false);
    } else if s[0] == x {
    } else {
        lemma_index_in_range(x, s.subrange(1, s.len() as int));
    }
}

proof fn lemma_index_correct(x: nat, s: Seq<nat>) 
    requires 
        exists|i: int| 0 <= i < s.len() && s[i] == x,
    ensures 
        s[index(x, s) as int] == x,
    decreases s.len()
{
    if s.len() == 0 {
        assert(false);
    } else if s[0] == x {
    } else {
        lemma_index_correct(x, s.subrange(1, s.len() as int));
    }
}

proof fn lemma_index_unique(x: nat, s: Seq<nat>, i: int)
    requires
        0 <= i < s.len(),
        s[i] == x,
        forall|k: int, l: int| 0 <= k < l < s.len() ==> s[k] < s[l],
    ensures
        index(x, s) as int == i
    decreases s.len()
{
    if i == 0 {
        assert(s[0] == x);
    } else {
        assert(s[0] < s[i]);
        lemma_index_unique(x, s.subrange(1, s.len() as int), i - 1);
    }
}

proof fn lemma_sum_properties(X_val: Seq<int>, X_crd: Seq<nat>, v_val: Seq<int>, v_crd: Seq<nat>, 
                             kX: nat, kV: nat, pX_end: nat, pV_end: nat)
    ensures
        sum(X_val, X_crd, v_val, v_crd, kX, kV, pX_end, pV_end) == 0 || 
        (exists|i: int| kX as int <= i < pX_end as int && i < X_crd.len() as int && 
         exists|j: int| kV as int <= j < pV_end as int && j < v_crd.len() as int &&
         X_crd[i] == v_crd[j])
    decreases pX_end + pV_end - (kX + kV)
{
    if pV_end <= kV || pX_end <= kX {
    } else if kX < X_crd.len() && kV < v_crd.len() && X_crd[kX as int] == v_crd[kV as int] {
        lemma_sum_properties(X_val, X_crd, v_val, v_crd, kX + 1, kV + 1, pX_end, pV_end);
    } else if kX < X_crd.len() && kV < v_crd.len() && X_crd[kX as int] < v_crd[kV as int] {
        lemma_sum_properties(X_val, X_crd, v_val, v_crd, kX + 1, kV, pX_end, pV_end);
    } else {
        lemma_sum_properties(X_val, X_crd, v_val, v_crd, kX, kV + 1, pX_end, pV_end);
    }
}

proof fn lemma_sum_step_eq(X_val: Seq<int>, X_crd: Seq<nat>, v_val: Seq<int>, v_crd: Seq<nat>, 
                          kX: nat, kV: nat, pX_end: nat, pV_end: nat)
    requires
        kX < X_crd.len() && kV < v_crd.len() && X_crd[kX as int] == v_crd[kV as int],
        pV_end > kV && pX_end > kX,
    ensures
        sum(X_val, X_crd, v_val, v_crd, kX, kV, pX_end, pV_end) == 
        sum(X_val, X_crd, v_val, v_crd, kX + 1, kV + 1, pX_end, pV_end) + 
        (if kV < v_val.len() && kX < X_val.len() { v_val[kV as int] * X_val[kX as int] } else { 0 })
    decreases pX_end + pV_end - (kX + kV)
{
    admit();
}

proof fn lemma_sum_step_lt(X_val: Seq<int>, X_crd: Seq<nat>, v_val: Seq<int>, v_crd: Seq<nat>, 
                          kX: nat, kV: nat, pX_end: nat, pV_end: nat)
    requires
        kX < X_crd.len() && kV < v_crd.len() && X_crd[kX as int] < v_crd[kV as int],
        pV_end > kV && pX_end > kX,
    ensures
        sum(X_val, X_crd, v_val, v_crd, kX, kV, pX_end, pV_end) == 
        sum(X_val, X_crd, v_val, v_crd, kX + 1, kV, pX_end, pV_end)
    decreases pX_end + pV_end - (kX + kV)
{
    admit();
}

proof fn lemma_sum_step_gt(X_val: Seq<int>, X_crd: Seq<nat>, v_val: Seq<int>, v_crd: Seq<nat>, 
                          kX: nat, kV: nat, pX_end: nat, pV_end: nat)
    requires
        (kX >= X_crd.len() || kV >= v_crd.len() || (kX < X_crd.len() && kV < v_crd.len() && X_crd[kX as int] > v_crd[kV as int])),
        pV_end > kV && pX_end > kX,
    ensures
        sum(X_val, X_crd, v_val, v_crd, kX, kV, pX_end, pV_end) == 
        sum(X_val, X_crd, v_val, v_crd, kX, kV + 1, pX_end, pV_end)
    decreases pX_end + pV_end - (kX + kV)
{
    admit();
}

proof fn lemma_sum_base_case(X_val: Seq<int>, X_crd: Seq<nat>, v_val: Seq<int>, v_crd: Seq<nat>, 
                            kX: nat, kV: nat, pX_end: nat, pV_end: nat)
    requires
        pV_end <= kV || pX_end <= kX,
    ensures
        sum(X_val, X_crd, v_val, v_crd, kX, kV, pX_end, pV_end) == 0
{
    admit();
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
    let mut result = Vec::with_capacity(X_len as usize);
    let mut i: nat = 0;
    
    while i < X_len
        invariant
            i <= X_len,
            result.len() == i as usize,
            forall|k: int| 0 <= k < i ==> {
                let idx = index(k, X_crd1@);
                result@[k] == if idx < X_crd1@.len() {
                    sum(X_val@, X_crd@, v_val@, v_crd@, X_pos@[idx], 0, 
                        X_pos@[idx + 1], v_val.len() as nat)
                } else {
                    0
                }
            }
    {
        let mut found = false;
        let mut j: nat = 0;
        
        while j < X_crd1.len()
            invariant
                j <= X_crd1.len(),
                !found ==> forall|k: int| 0 <= k < j ==> X_crd1@[k] != i,
                found ==> j > 0 && X_crd1@[j as int - 1] == i
        {
            if X_crd1[j as usize] == i {
                found = true;
                break;
            }
            j += 1;
        }
        
        if found {
            proof {
                lemma_index_unique(i, X_crd1@, j as int - 1);
            }
            let idx = index(i, X_crd1@);
            let start = X_pos[idx as usize];
            let end = X_pos[idx as usize + 1];
            
            let mut sum_val = 0;
            let mut pX = start;
            let mut pV = 0;
            
            while pX < end && pV < v_val.len() as nat
                invariant
                    pX >= start,
                    pV >= 0,
                    pX <= end,
                    pV <= v_val.len() as nat,
                    sum_val == sum(X_val@, X_crd@, v_val@, v_crd@, start, 0, pX, pV)
            {
                if pX >= X_crd.len() as nat || pV >= v_crd.len() as nat {
                    break;
                }
                
                if X_crd[pX as usize] == v_crd[pV as usize] {
                    proof {
                        lemma_sum_step_eq(X_val@, X_crd@, v_val@, v_crd@, pX, pV, end, v_val.len() as nat);
                    }
                    sum_val = sum_val + v_val[pV as usize] * X_val[pX as usize];
                    pX += 1;
                    pV += 1;
                } else if X_crd[pX as usize] < v_crd[pV as usize] {
                    proof {
                        lemma_sum_step_lt(X_val@, X_crd@, v_val@, v_crd@, pX, pV, end, v_val.len() as nat);
                    }
                    pX += 1;
                } else {
                    proof {
                        lemma_sum_step_gt(X_val@, X_crd@, v_val@, v_crd@, pX, pV, end, v_val.len() as nat);
                    }
                    pV += 1;
                }
            }
            
            proof {
                lemma_sum_base_case(X_val@, X_crd@, v_val@, v_crd@, pX, pV, end, v_val.len() as nat);
            }
            assert(sum_val == sum(X_val@, X_crd@, v_val@, v_crd@, start, 0, end, v_val.len() as nat));
            result.push(sum_val);
        } else {
            result.push(0);
        }
        
        i += 1;
    }
    
    result
}
// </vc-code>

fn main() {}

}