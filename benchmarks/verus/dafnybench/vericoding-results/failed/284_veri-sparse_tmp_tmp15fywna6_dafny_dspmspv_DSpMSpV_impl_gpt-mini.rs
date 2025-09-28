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
// Helper lemmas to assist verification of indexing and monotonicity

proof fn pos_consecutive_bounds(X_crd1: Seq<nat>, X_pos: Seq<nat>, idx: nat)
    requires X_crd1.len() < X_pos.len(),
             idx < X_crd1.len(),
    ensures (idx as int) + 1 < X_pos.len()
{
    // work in int domain for comparisons
    assert(idx as int < X_crd1.len());
    // from idx < X_crd1.len() we get idx+1 <= X_crd1.len()
    assert(idx as int + 1 <= X_crd1.len());
    assert(X_crd1.len() < X_pos.len());
    // chain to get strict inequality
    assert(idx as int + 1 < X_pos.len());
}

proof fn pos_monotone_consecutive(X_pos: Seq<nat>, idx: nat)
    requires (idx as int) + 1 < X_pos.len(),
             forall|i: int, j: int| 0 <= i < j < X_pos.len() ==> X_pos[i] <= X_pos[j],
    ensures X_pos[idx as int] <= X_pos[idx as int + 1]
{
    // instantiate the quantified monotonicity for i = idx, j = idx + 1
    assert(0 <= idx as int);
    assert(idx as int + 1 < X_pos.len());
    assert(X_pos[idx as int] <= X_pos[idx as int + 1]);
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
    let mut i: nat = 0;
    let pV_end: nat = v_val.len() as nat;

    while i < X_len {
        invariant 0 <= i && i <= X_len;
        invariant result.len() as nat == i;
        invariant forall|j: int|
            0 <= j < (result@).len() ==>
                #[trigger] result@[j] == if index(j as nat, X_crd1@) < X_crd1.len() {
                    sum(X_val@, X_crd@, v_val@, v_crd@,
                        X_pos[index(j as nat, X_crd1@) as int],
                        0,
                        X_pos[index(j as nat, X_crd1@) as int + 1],
                        pV_end)
                } else {
                    0
                };

        let idx = index(i as nat, X_crd1@);
        if idx < X_crd1.len() {
            // justify that idx + 1 < X_pos.len() so we can index X_pos[idx+1]
            proof {
                pos_consecutive_bounds(X_crd1@, X_pos@, idx);
            }

            let start: nat = X_pos[idx as int];
            let end: nat = X_pos[idx as int + 1];

            // monotonicity ensures start <= end
            proof {
                pos_monotone_consecutive(X_pos@, idx);
            }

            // compute row sum via two-pointer merge
            let mut kX: nat = start;
            let mut kV: nat = 0;
            let mut s: int = 0;

            // loop while both pointers are within their effective ranges
            while kX < end && kV < pV_end {
                invariant start <= kX && kX <= end;
                invariant 0 <= kV && kV <= pV_end;
                invariant s + sum(X_val@, X_crd@, v_val@, v_crd@, kX, kV, end, pV_end)
                          == sum(X_val@, X_crd@, v_val@, v_crd@, start, 0, end, pV_end);

                if kX < X_crd.len() && kV < v_crd.len() && X_crd[kX as int] == v_crd[kV as int] {
                    // use the definition of sum to update the invariant
                    proof {
                        // conditions to unfold the recursive branch of sum
                        assert(pV_end > kV);
                        assert((end as int) > kX as int);
                        // unfold the sum for these indices according to its spec
                        assert(sum(X_val@, X_crd@, v_val@, v_crd@, kX, kV, end, pV_end)
                               == sum(X_val@, X_crd@, v_val@, v_crd@, kX + 1, kV + 1, end, pV_end)
                                  + (if kV < v_val.len() && kX < X_val.len() { v_val[kV as int] * X_val[kX as int] } else { 0 }));
                        // now use the invariant to relate s'
                        assert(s + (if kV < v_val.len() && kX < X_val.len() { v_val[kV as int] * X_val[kX as int] } else { 0 })
                               + sum(X_val@, X_crd@, v_val@, v_crd@, kX + 1, kV + 1, end, pV_end)
                               == sum(X_val@, X_crd@, v_val@, v_crd@, start, 0, end, pV_end));
                    }

                    s = s + v_val[kV as int] * X_val[kX as int];
                    kX = kX + 1;
                    kV = kV + 1;
                } else if kX < X_crd.len() && kV < v_crd.len() && X_crd[kX as int] < v_crd[kV as int] {
                    // when advancing kX, sum(...) simply advances kX without adding to s
                    proof {
                        assert(pV_end > kV);
                        assert((end as int) > kX as int);
                        assert(sum(X_val@, X_crd@, v_val@, v_crd@, kX, kV, end, pV_end)
                               == sum(X_val@, X_crd@, v_val@, v_crd@, kX + 1, kV, end, pV_end));
                        assert(s + sum(X_val@, X_crd@, v_val@, v_crd@, kX + 1, kV, end, pV_end)
                               == sum(X_val@, X_crd@, v_val@, v_crd@, start, 0, end, pV_end));
                    }
                    kX = kX + 1;
                } else {
                    // advancing kV
                    proof {
                        assert(pV_end > kV);
                        assert(sum(X_val@, X_crd@, v_val@, v_crd@, kX, kV, end, pV_end)
                               == sum(X_val@, X_crd@, v_val@, v_crd@, kX, kV + 1, end, pV_end));
                        assert(s + sum(X_val@, X_crd@, v_val@, v_crd@, kX, kV + 1, end, pV_end)
                               == sum(X_val@, X_crd@, v_val@, v_crd@, start, 0, end, pV_end));
                    }
                    kV = kV + 1;
                }
            }

            // After loop, s equals the spec sum starting at `start`
            assert(s == sum(X_val@, X_crd@, v_val@, v_crd@, start, 0, end, pV_end));
            result.push(s);
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