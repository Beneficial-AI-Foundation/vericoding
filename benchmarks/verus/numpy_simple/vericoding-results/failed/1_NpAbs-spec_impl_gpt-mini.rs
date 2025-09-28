// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn abs_int(x: int) -> int {
    if x < 0 { -x } else { x }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): prove abs non-negativity */
proof fn lemma_abs_nonneg(x: i8)
    ensures
        abs_int(x as int) >= 0,
{
    assert(abs_int(x as int) >= 0);
}

/* helper modified by LLM (iteration 2): prove abs correctness */
proof fn lemma_abs_correctness(x: i8)
    ensures
        abs_int(x as int) == if x as int < 0 { -(x as int) } else { x as int },
{
    assert(abs_int(x as int) == if x as int < 0 { -(x as int) } else { x as int });
}

// </vc-helpers>

// <vc-spec>
fn abs(a: Vec<i8>) -> (result: Vec<i8>)
    ensures 
        result.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> result[i] as int == abs_int(a[i] as int),
        forall|i: int| 0 <= i < result.len() ==> result[i] >= 0,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): compute element-wise absolute preserving spec */
    let mut result: Vec<i8> = Vec::new();
    let n: int = a.len();
    let mut i: int = 0;
    while i < n
        invariant
            0 <= i,
            i <= n,
            result.len() == i,
        decreases n - i
    {
        let ai: i8 = a[i];
        proof {
            lemma_abs_correctness(ai);
            lemma_abs_nonneg(ai);
        }
        let ai_abs_int: int = if ai as int < 0 { -(ai as int) } else { ai as int };
        let ri: i8 = ai_abs_int as i8;
        result.push(ri);
        i += 1;
    }
    result
}
// </vc-code>


}
fn main() {}