// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
proof fn lemma_abs_zero_iff(x: int)
    ensures
        abs_spec(x) == 0 <==> x == 0,
{
    if x == 0 {
        assert(abs_spec(x) == 0);
    } else if x > 0 {
        assert(abs_spec(x) == x);
        assert(abs_spec(x) != 0);
    } else {
        assert(x < 0);
        assert(-x > 0);
        assert(abs_spec(x) == -x);
        assert(abs_spec(x) != 0);
    }
}

proof fn lemma_i8_cast_identity(n: int)
    requires
        0 <= n,
        n <= 127,
    ensures
        (n as i8) as int == n,
{
}

proof fn lemma_i8_eq_zero_iff_int_eq_zero(v: i8)
    ensures
        (v == 0) <==> ((v as int) == 0),
{
}

proof fn lemma_abs_i8_in_range(v: i8)
    ensures
        0 <= abs_spec(v as int),
        abs_spec(v as int) <= 127,
{
    let vi = v as int;
    if vi >= 0 {
        assert(abs_spec(vi) == vi);
        assert(0 <= vi);
        assert(vi <= 127);
    } else {
        assert(abs_spec(vi) == -vi);
        assert(0 <= -vi);
        assert(-vi <= 127);
    }
}
// </vc-helpers>

// <vc-spec>
spec fn abs_spec(x: int) -> int {
    if x >= 0 { x } else { -x }
}

fn absolute(x: Vec<i8>) -> (result: Vec<i8>)
    ensures 
        result.len() == x.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i] as int == abs_spec(x[i] as int),
        forall|i: int| 0 <= i < result.len() ==> result[i] >= 0,
        forall|i: int| 0 <= i < result.len() ==> (result[i] == 0 <==> x[i] == 0)
// </vc-spec>
// <vc-code>
{
    let n = x.len();
    let mut result: Vec<i8> = Vec::new();
    result.reserve(n);
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            result.len() == i,
            forall|j: int| 0 <= j < i as int ==> result@[j] as int == abs_spec(x@[j] as int),
            forall|j: int| 0 <= j < i as int ==> result@[j] >= 0,
            forall|j: int| 0 <= j < i as int ==> (result@[j] == 0) <==> (x@[j] == 0),
        decreases n - i
    {
        let v = x[i];
        let vi: int = v as int;
        let ai: int = abs_spec(vi);
        proof {
            lemma_abs_i8_in_range(v);
        }
        assert(0 <= ai && ai <= 127);
        let y: i8 = ai as i8;
        proof {
            lemma_i8_cast_identity(ai);
            lemma_abs_zero_iff(vi);
            lemma_i8_eq_zero_iff_int_eq_zero(v);
            lemma_i8_eq_zero_iff_int_eq_zero(y);
        }
        result.push(y);
        i = i + 1;
    }
    result
}
// </vc-code>


}
fn main() {}