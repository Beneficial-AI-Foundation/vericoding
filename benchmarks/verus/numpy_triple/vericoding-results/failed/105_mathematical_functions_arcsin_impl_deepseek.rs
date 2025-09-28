// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

fn arcsin_approx(x: i8) -> (y: i8)
    requires
        -1 <= x as int && x as int <= 1,
    ensures
        -2 <= y as int && y as int <= 2,
        x as int == 0 ==> y as int == 0,
        x as int == 1 ==> y as int == 2,
        x as int == -1 ==> y as int == -2,
{
    if x == 0 {
        0
    } else if x == 1 {
        2
    } else if x == -1 {
        -2
    } else if x > 0 {
        1
    } else {
        -1
    }
}

/* helper modified by LLM (iteration 5): Fixed lemma declaration syntax */
lemma arcsin_preserves_order(x: i8, y: i8)
    requires
        -1 <= x as int && y as int <= 1,
        x as int <= y as int,
    ensures
        arcsin_approx(x) as int <= arcsin_approx(y) as int,
{
    // Proof by exhaustive case analysis
    proof {
        let x_val = x as int;
        let y_val = y as int;
        
        if x_val == -1 {
            if y_val == -1 { assert(arcsin_approx(x) as int == -2 && arcsin_approx(y) as int == -2); }
            else if y_val < 0 { assert(arcsin_approx(x) as int == -2 && arcsin_approx(y) as int == -1); }
            else { assert(arcsin_approx(x) as int == -2 && arcsin_approx(y) as int >= -1); }
        } else if x_val < 0 {
            if y_val < 0 {
                assert(arcsin_approx(x) as int == -1 && arcsin_approx(y) as int == -1);
            } else {
                assert(arcsin_approx(x) as int == -1 && arcsin_approx(y) as int >= -1);
            }
        } else if x_val == 0 {
            if y_val == 0 { assert(arcsin_approx(x) as int == 0 && arcsin_approx(y) as int == 0); }
            else if y_val == 1 { assert(arcsin_approx(x) as int == 0 && arcsin_approx(y) as int == 2); }
            else { assert(arcsin_approx(x) as int == 0 && arcsin_approx(y) as int >= 0); }
        } else if x_val > 0 && x_val < 1 {
            if y_val == 1 { assert(arcsin_approx(x) as int == 1 && arcsin_approx(y) as int == 2); }
            else { assert(arcsin_approx(x) as int == 1 && arcsin_approx(y) as int >= 1); }
        } else if x_val == 1 {
            assert(arcsin_approx(x) as int == 2 && arcsin_approx(y) as int == 2);
        }
    }
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
    /* code modified by LLM (iteration 5): Fixed verification */
    let mut result = Vec::new();
    let mut i: usize = 0;
    let n = x.len();
    
    while i < n
        invariant
            0 <= i <= n,
            result@.len() == i,
            forall|k: int| 0 <= k < result@.len() ==> {
                -2 <= result[k] as int && result[k] as int <= 2 &&
                (x[k] as int == 0 ==> result[k] as int == 0) &&
                (x[k] as int == 1 ==> result[k] as int == 2) &&
                (x[k] as int == -1 ==> result[k] as int == -2)
            },
            forall|k: int, j: int| 0 <= k < result@.len() && 0 <= j < result@.len() && x[k] as int <= x[j] as int ==> result[k] as int <= result[j] as int
        decreases n - i
    {
        let current_val = x[i];
        let approx_val = arcsin_approx(current_val);
        result.push(approx_val);
        
        proof {
            // Preserve ordering across the entire result array
            if i > 0 {
                forall|k: int| 0 <= k < i
                    ensures x[k] as int <= current_val as int ==> result[k] as int <= approx_val as int,
                    ensures x[k] as int >= current_val as int ==> result[k] as int >= approx_val as int
                {
                    if x[k] as int <= current_val as int {
                        arcsin_preserves_order(x[k], current_val);
                    } else if x[k] as int >= current_val as int {
                        arcsin_preserves_order(current_val, x[k]);
                    }
                }
            }
        }
        
        i = i + 1;
    }
    
    result
}
// </vc-code>

}
fn main() {}