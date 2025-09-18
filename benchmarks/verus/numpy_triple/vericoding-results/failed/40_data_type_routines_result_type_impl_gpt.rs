// <vc-preamble>
use vstd::prelude::*;

verus! {

#[derive(PartialEq, Eq, Structural)]
pub enum NumpyDType {

    Int8,

    Int16,

    Int32,

    Int64,

    Float32,

    Float64,

    Complex64,

    Complex128,

    Bool,
}

spec fn type_rank(dtype: NumpyDType) -> nat {
    match dtype {
        NumpyDType::Bool => 0,
        NumpyDType::Int8 => 1,
        NumpyDType::Int16 => 2,
        NumpyDType::Int32 => 3,
        NumpyDType::Int64 => 4,
        NumpyDType::Float32 => 5,
        NumpyDType::Float64 => 6,
        NumpyDType::Complex64 => 7,
        NumpyDType::Complex128 => 8,
    }
}

pub enum NumpyOperand {

    Scalar(NumpyDType),

    Array(NumpyDType, Vec<i32>),
}

spec fn operand_type(operand: NumpyOperand) -> NumpyDType {
    match operand {
        NumpyOperand::Scalar(dtype) => dtype,
        NumpyOperand::Array(dtype, _) => dtype,
    }
}

spec fn promote_types(t1: NumpyDType, t2: NumpyDType) -> NumpyDType {
    if type_rank(t1) >= type_rank(t2) { t1 } else { t2 }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): exec rank mirroring the spec rank */
fn rank_exec(dtype: NumpyDType) -> (res: usize)
    ensures res as nat == type_rank(dtype)
{
    match dtype {
        NumpyDType::Bool => 0usize,
        NumpyDType::Int8 => 1usize,
        NumpyDType::Int16 => 2usize,
        NumpyDType::Int32 => 3usize,
        NumpyDType::Int64 => 4usize,
        NumpyDType::Float32 => 5usize,
        NumpyDType::Float64 => 6usize,
        NumpyDType::Complex64 => 7usize,
        NumpyDType::Complex128 => 8usize,
    }
}

/* helper modified by LLM (iteration 5): pick the dtype with maximal rank using exec rank */
fn max_of_two(a: NumpyDType, b: NumpyDType) -> (res: NumpyDType)
    ensures
        type_rank(res) >= type_rank(a),
        type_rank(res) >= type_rank(b),
        type_rank(res) == type_rank(a) || type_rank(res) == type_rank(b)
{
    let ra = rank_exec(a);
    let rb = rank_exec(b);
    if ra >= rb {
        proof {
            assert(ra as nat == type_rank(a));
            assert(rb as nat == type_rank(b));
            assert(type_rank(a) >= type_rank(b));
        }
        a
    } else {
        proof {
            assert(ra as nat == type_rank(a));
            assert(rb as nat == type_rank(b));
            assert(type_rank(b) >= type_rank(a));
        }
        b
    }
}

/* helper modified by LLM (iteration 5): recursive fold over a prefix providing bounds and existence of a witness */
fn fold_max_with_witness(operands: &Vec<NumpyOperand>, end: usize) -> (res: NumpyDType)
    requires 1 <= end && end <= operands.len()
    ensures
        forall|k: int| 0 <= k < end as int ==> type_rank(res) >= type_rank(operand_type(operands[k])),
        exists|w: int| 0 <= w < end as int && type_rank(res) == type_rank(operand_type(operands[w]))
    decreases end as int
{
    if end == 1usize {
        match operands[0] {
            NumpyOperand::Scalar(d) => d,
            NumpyOperand::Array(d, _) => d,
        }
    } else {
        let prev = fold_max_with_witness(operands, end - 1usize);
        let idx = end - 1usize;
        let di = match operands[idx] {
            NumpyOperand::Scalar(d) => d,
            NumpyOperand::Array(d, _) => d,
        };
        let r = max_of_two(prev, di);
        let idx_int: int = idx as int;
        proof {
            // Propagate bound to indices < end-1
            assert(forall|k: int| 0 <= k && k < (end - 1usize) as int ==> type_rank(prev) >= type_rank(operand_type(operands[k])));
            assert(forall|k: int| 0 <= k && k < (end - 1usize) as int ==> type_rank(r) >= type_rank(operand_type(operands[k]))) by {
                assert forall|k: int| 0 <= k && k < (end - 1usize) as int ==> type_rank(r) >= type_rank(operand_type(operands[k])) {
                    if 0 <= k && k < (end - 1usize) as int {
                        assert(type_rank(prev) >= type_rank(operand_type(operands[k])));
                        assert(type_rank(r) >= type_rank(prev));
                        assert(type_rank(r) >= type_rank(operand_type(operands[k])));
                    }
                }
            }
            // Relate last element's operand_type to di
            match operands[idx] {
                NumpyOperand::Scalar(d) => { assert(di == d); assert(operand_type(operands[idx_int]) == d); }
                NumpyOperand::Array(d, _) => { assert(di == d); assert(operand_type(operands[idx_int]) == d); }
            }
            assert(type_rank(r) >= type_rank(di));
            assert(type_rank(r) >= type_rank(operand_type(operands[idx_int])));
            // Combine into bound for all k < end
            assert(forall|k: int| 0 <= k && k < end as int ==> type_rank(r) >= type_rank(operand_type(operands[k]))) by {
                assert forall|k: int| 0 <= k && k < end as int ==> type_rank(r) >= type_rank(operand_type(operands[k])) {
                    if 0 <= k && k < end as int {
                        if k < (end - 1usize) as int {
                            assert(type_rank(r) >= type_rank(operand_type(operands[k])));
                        } else {
                            assert(k == idx_int);
                            assert(type_rank(r) >= type_rank(operand_type(operands[idx_int])));
                        }
                    }
                }
            }
            // Existence witness
            let wprev = choose|w: int|
                0 <= w && w < (end - 1usize) as int
                && type_rank(prev) == type_rank(operand_type(operands[w]));
            assert(type_rank(r) == type_rank(prev) || type_rank(r) == type_rank(di));
            if type_rank(r) == type_rank(prev) {
                assert(0 <= wprev && wprev < end as int);
                assert(type_rank(r) == type_rank(operand_type(operands[wprev])));
                assert(exists|w: int| w == wprev && 0 <= w && w < end as int
                    && type_rank(r) == type_rank(operand_type(operands[w])));
            } else {
                assert(type_rank(r) == type_rank(di));
                let wlast: int = idx_int;
                assert(0 <= wlast && wlast < end as int);
                assert(operand_type(operands[wlast]) == di);
                assert(type_rank(r) == type_rank(operand_type(operands[wlast])));
                assert(exists|w: int| w == wlast && 0 <= w && w < end as int
                    && type_rank(r) == type_rank(operand_type(operands[w])));
            }
        }
        r
    }
}

/* helper modified by LLM (iteration 5): lemma that an upper bound of both is an upper bound of promote_types */
proof fn promote_max_upper_bound(a: NumpyDType, b: NumpyDType, ub: NumpyDType)
    requires type_rank(ub) >= type_rank(a), type_rank(ub) >= type_rank(b)
    ensures type_rank(ub) >= type_rank(promote_types(a, b))
{
    if type_rank(a) >= type_rank(b) {
        assert(promote_types(a, b) == a);
    } else {
        assert(promote_types(a, b) == b);
    }
}
// </vc-helpers>

// <vc-spec>
fn result_type(operands: Vec<NumpyOperand>) -> (result: NumpyDType)
    requires operands.len() > 0,
    ensures

        forall|i: int| 0 <= i < operands.len() ==> 
            type_rank(result) >= type_rank(operand_type(operands[i])),

        exists|i: int| 0 <= i < operands.len() && 
            type_rank(result) == type_rank(operand_type(operands[i])),

        forall|i: int, j: int| 0 <= i < operands.len() && 0 <= j < operands.len() ==>
            type_rank(result) >= type_rank(promote_types(operand_type(operands[i]), operand_type(operands[j]))),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fold to compute maximal dtype and prove promotion upper bound */
    let n = operands.len();
    let res = fold_max_with_witness(&operands, n);
    proof {
        let n_int = n as int;
        assert(forall|i: int, j: int|
            0 <= i && i < n_int && 0 <= j && j < n_int ==>
                type_rank(res) >= type_rank(promote_types(operand_type(operands[i]), operand_type(operands[j])))) by {
            assert forall|i: int, j: int|
                0 <= i && i < n_int && 0 <= j && j < n_int ==>
                    type_rank(res) >= type_rank(promote_types(operand_type(operands[i]), operand_type(operands[j]))) {
                if 0 <= i && i < n_int && 0 <= j && j < n_int {
                    assert(type_rank(res) >= type_rank(operand_type(operands[i])));
                    assert(type_rank(res) >= type_rank(operand_type(operands[j])));
                    promote_max_upper_bound(operand_type(operands[i]), operand_type(operands[j]), res);
                }
            }
        }
    }
    res
}
// </vc-code>

}
fn main() {}