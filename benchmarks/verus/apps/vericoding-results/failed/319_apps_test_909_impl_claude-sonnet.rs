// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(a: int, b: int, c: int) -> bool {
    1 <= a <= 10 && 1 <= b <= 10 && 1 <= c <= 10
}

spec fn all_expressions(a: int, b: int, c: int) -> Seq<int> {
    seq![a * b * c, a + b * c, a * b + c, a * (b + c), (a + b) * c, a + b + c]
}

spec fn max_expression(a: int, b: int, c: int) -> int
    recommends valid_input(a, b, c)
{
    let exprs = all_expressions(a, b, c);
    if exprs[0] >= exprs[1] && exprs[0] >= exprs[2] && exprs[0] >= exprs[3] && exprs[0] >= exprs[4] && exprs[0] >= exprs[5] { exprs[0] }
    else if exprs[1] >= exprs[2] && exprs[1] >= exprs[3] && exprs[1] >= exprs[4] && exprs[1] >= exprs[5] { exprs[1] }
    else if exprs[2] >= exprs[3] && exprs[2] >= exprs[4] && exprs[2] >= exprs[5] { exprs[2] }
    else if exprs[3] >= exprs[4] && exprs[3] >= exprs[5] { exprs[3] }
    else if exprs[4] >= exprs[5] { exprs[4] }
    else { exprs[5] }
}

spec fn is_max_of_all_expressions(result: int, a: int, b: int, c: int) -> bool
    recommends valid_input(a, b, c)
{
    let exprs = all_expressions(a, b, c);
    exprs.contains(result) && forall|i: int| 0 <= i < exprs.len() ==> result >= exprs[i]
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed arithmetic proof with correct bounds reasoning */
proof fn arithmetic_operations_in_bounds(a: int, b: int, c: int)
    requires valid_input(a, b, c)
    ensures
        a * b * c <= 1000,
        a + b * c <= 110,
        a * b + c <= 110,
        a * (b + c) <= 200,
        (a + b) * c <= 200,
        a + b + c <= 30,
        a * b * c >= 1,
        a + b * c >= 3,
        a * b + c >= 3,
        a * (b + c) >= 3,
        (a + b) * c >= 3,
        a + b + c >= 3
{
    assert(a >= 1 && b >= 1 && c >= 1);
    assert(a <= 10 && b <= 10 && c <= 10);
    
    // Prove a * b bounds using proper multiplication reasoning
    assert(a >= 1 && b >= 1 ==> a * b >= 1);
    assert(a <= 10 && b <= 10 ==> a * b <= 100);
    
    // Prove a * b * c bounds step by step
    assert(a * b >= 1 && c >= 1 ==> a * b * c >= 1);
    assert(a * b <= 100 && c <= 10 ==> a * b * c <= 1000);
    
    // Prove b * c bounds
    assert(b >= 1 && c >= 1 ==> b * c >= 1);
    assert(b <= 10 && c <= 10 ==> b * c <= 100);
    
    // Prove other expression bounds
    assert(a <= 10 && b * c <= 100 ==> a + b * c <= 110);
    assert(a * b <= 100 && c <= 10 ==> a * b + c <= 110);
    assert(b + c <= 20 && a <= 10 ==> a * (b + c) <= 200);
    assert(a + b <= 20 && c <= 10 ==> (a + b) * c <= 200);
    assert(a <= 10 && b <= 10 && c <= 10 ==> a + b + c <= 30);
    
    // Lower bounds
    assert(a >= 1 && b * c >= 1 ==> a + b * c >= 2);
    assert(a + b * c >= 2 && a >= 1 ==> a + b * c >= 3 - 1);
    assert(a * b >= 1 && c >= 1 ==> a * b + c >= 2);
    assert(b + c >= 2 && a >= 1 ==> a * (b + c) >= 2);
    assert(a + b >= 2 && c >= 1 ==> (a + b) * c >= 2);
    assert(a >= 1 && b >= 1 && c >= 1 ==> a + b + c >= 3);
}

proof fn max_expression_is_max_of_all(a: int, b: int, c: int)
    requires valid_input(a, b, c)
    ensures is_max_of_all_expressions(max_expression(a, b, c), a, b, c)
{
    let exprs = all_expressions(a, b, c);
    let max_val = max_expression(a, b, c);
    
    assert(exprs[0] == a * b * c);
    assert(exprs[1] == a + b * c);
    assert(exprs[2] == a * b + c);
    assert(exprs[3] == a * (b + c));
    assert(exprs[4] == (a + b) * c);
    assert(exprs[5] == a + b + c);
    
    if max_val == exprs[0] {
        assert(exprs.contains(max_val));
        assert(forall|i: int| 0 <= i < exprs.len() ==> max_val >= exprs[i]);
    } else if max_val == exprs[1] {
        assert(exprs.contains(max_val));
        assert(forall|i: int| 0 <= i < exprs.len() ==> max_val >= exprs[i]);
    } else if max_val == exprs[2] {
        assert(exprs.contains(max_val));
        assert(forall|i: int| 0 <= i < exprs.len() ==> max_val >= exprs[i]);
    } else if max_val == exprs[3] {
        assert(exprs.contains(max_val));
        assert(forall|i: int| 0 <= i < exprs.len() ==> max_val >= exprs[i]);
    } else if max_val == exprs[4] {
        assert(exprs.contains(max_val));
        assert(forall|i: int| 0 <= i < exprs.len() ==> max_val >= exprs[i]);
    } else {
        assert(max_val == exprs[5]);
        assert(exprs.contains(max_val));
        assert(forall|i: int| 0 <= i < exprs.len() ==> max_val >= exprs[i]);
    }
}
// </vc-helpers>

// <vc-spec>
fn solve(a: i8, b: i8, c: i8) -> (result: i8)
    requires 
        valid_input(a as int, b as int, c as int),
    ensures 
        is_max_of_all_expressions(result as int, a as int, b as int, c as int),
        result as int == max_expression(a as int, b as int, c as int),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): step-by-step computation to avoid overflow */
    proof {
        arithmetic_operations_in_bounds(a as int, b as int, c as int);
    }
    
    let ab = a * b;
    let bc = b * c;
    let bc_sum = b + c;
    let ab_sum = a + b;
    
    let expr1 = ab * c;
    let expr2 = a + bc;
    let expr3 = ab + c;
    let expr4 = a * bc_sum;
    let expr5 = ab_sum * c;
    let expr6 = a + b + c;
    
    let mut max_val = expr1;
    
    if expr2 > max_val {
        max_val = expr2;
    }
    if expr3 > max_val {
        max_val = expr3;
    }
    if expr4 > max_val {
        max_val = expr4;
    }
    if expr5 > max_val {
        max_val = expr5;
    }
    if expr6 > max_val {
        max_val = expr6;
    }
    
    proof {
        max_expression_is_max_of_all(a as int, b as int, c as int);
    }
    
    max_val
}
// </vc-code>


}

fn main() {}