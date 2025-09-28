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
proof fn index_upper_bound(x: nat, y: Seq<nat>)
    ensures index(x, y) <= y.len() as nat
    decreases y.len()
{
    if y.len() == 0 {
        assert(index(x, y) == 0);
    } else {
        if y[0] == x {
            assert(index(x, y) == 0);
        } else {
            index_upper_bound(x, y.subrange(1, y.len() as int));
            assert(y.subrange(1, y.len() as int).len() == y.len() - 1);
            assert(index(x, y.subrange(1, y.len() as int)) <= (y.len() - 1) as nat);
            assert(1 + index(x, y.subrange(1, y.len() as int)) <= y.len() as nat);
            assert(index(x, y) == 1 + index(x, y.subrange(1, y.len() as int)));
        }
    }
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
    let s: Seq<int> = Seq::new(X_len as int, |i: int| {
        assert(0 <= i);
        let idx: nat = index(i as nat, X_crd1@);
        if idx < X_crd1.len() {
            let idx_i: int = idx as int;
            let xcrd1_len: nat = X_crd1.len();
            let xpos_len: nat = X_pos.len();
            assert(0 <= idx_i);
            assert(idx_i < xcrd1_len as int);
            assert(xcrd1_len < xpos_len);
            assert(idx_i < xpos_len as int) by {
                assert(idx_i < xcrd1_len as int);
                assert(xcrd1_len as int < xpos_len as int);
            }
            assert(idx_i + 1 <= xcrd1_len as int);
            assert(idx_i + 1 < xpos_len as int) by {
                assert(idx_i + 1 <= xcrd1_len as int);
                assert(xcrd1_len as int < xpos_len as int);
            }
            sum(
                X_val@, X_crd@, v_val@, v_crd@,
                X_pos@[idx_i], 0, X_pos@[idx_i + 1], v_val.len()
            )
        } else {
            0
        }
    });
    Vec::from_seq(s)
}
// </vc-code>

fn main() {}

}