// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn arcsin_i8_spec(x: i8) -> i8
{
    if x == 0 {
        0
    } else if x == 1 {
        2
    } else if x == -1 {
        -2
    } else {
        x * 2
    }
}

fn arcsin_i8(x: i8) -> (result: i8)
    requires
        -1 <= x as int && x as int <= 1,
    ensures
        result == arcsin_i8_spec(x),
        -2 <= result as int && result as int <= 2,
        (x as int == 0 ==> result as int == 0),
        (x as int == 1 ==> result as int == 2),
        (x as int == -1 ==> result as int == -2),
{
    if x == 0 {
        0
    } else if x == 1 {
        2
    } else if x == -1 {
        -2
    } else {
        x * 2
    }
}

/* helper modified by LLM (iteration 5): made lemma executable by using spec function */
proof fn lemma_arcsin_monotonic(x: i8, y: i8)
    requires
        -1 <= x as int && x as int <= 1,
        -1 <= y as int && y as int <= 1,
        x as int <= y as int,
    ensures
        arcsin_i8_spec(x) as int <= arcsin_i8_spec(y) as int,
{
}
// </vc-helpers>

// <vc-spec>
fn numpy_arcsin(x: Vec<i8>) -> (result: Vec<i8>)
    requires 
        x@.len() > 0,
        forall|i: int| 0 <= i < x@.len() ==> -1 <= x[i] as int && x[i] as int <= 1,
    ensures
        result@.len() == x@.len(),
        forall|i: int| 0 <= i < result@.len() ==> {
            -2 <= result[i] as int && result[i] as int <= 2 &&
            (x[i] as int == 0 ==> result[i] as int == 0) &&
            (x[i] as int == 1 ==> result[i] as int == 2) &&
            (x[i] as int == -1 ==> result[i] as int == -2)
        },
        forall|i: int, j: int| 0 <= i < x@.len() && 0 <= j < x@.len() && x[i] as int <= x[j] as int ==> result[i] as int <= result[j] as int
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed forall syntax in proof block */
    let mut result = Vec::new();
    let mut i = 0;
    
    while i < x.len()
        invariant
            0 <= i <= x@.len(),
            result@.len() == i,
            forall|j: int| 0 <= j < i ==> {
                -2 <= result[j] as int && result[j] as int <= 2 &&
                (x[j] as int == 0 ==> result[j] as int == 0) &&
                (x[j] as int == 1 ==> result[j] as int == 2) &&
                (x[j] as int == -1 ==> result[j] as int == -2)
            },
            forall|j1: int, j2: int| 0 <= j1 < i && 0 <= j2 < i && x[j1] as int <= x[j2] as int ==> result[j1] as int <= result[j2] as int,
    {
        let val = arcsin_i8(x[i]);
        proof {
            lemma_arcsin_monotonic(x[i], x[i]);
            forall|k: int| 0 <= k < i
                ensures
                    (x[k] as int <= x[i] as int ==> result[k] as int <= val as int),
                    (x[i] as int <= x[k] as int ==> val as int <= result[k] as int),
            {
                if x[k] as int <= x[i] as int {
                    lemma_arcsin_monotonic(x[k], x[i]);
                }
                if x[i] as int <= x[k] as int {
                    lemma_arcsin_monotonic(x[i], x[k]);
                }
            }
        }
        result.push(val);
        i += 1;
    }
    
    result
}
// </vc-code>

}
fn main() {}