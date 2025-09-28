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

proof fn lemma_max_property(exprs: Seq<int>, max_val: int)
    requires
        exprs.len() > 0,
        exprs.contains(max_val),
        forall|i: int| 0 <= i < exprs.len() ==> max_val >= exprs[i],
    ensures
        forall|i: int| 0 <= i < exprs.len() ==> max_val >= exprs[i],
{
}

proof fn lemma_all_expressions_non_empty(a: int, b: int, c: int)
    requires valid_input(a, b, c),
    ensures all_expressions(a, b, c).len() == 6,
{
}

proof fn lemma_max_exists_in_expressions(a: int, b: int, c: int) -> (max_val: int)
    requires valid_input(a, b, c),
    ensures
        is_max_of_all_expressions(max_val, a, b, c),
        max_val == max_expression(a, b, c),
{
    lemma_all_expressions_non_empty(a, b, c);
    max_val = max_expression(a, b, c);
}

proof fn lemma_expression_equivalences(a: int, b: int, c: int)
    requires valid_input(a, b, c),
    ensures
        all_expressions(a, b, c)@[0] == a * b * c,
        all_expressions(a, b, c)@[1] == a + b * c,
        all_expressions(a, b, c)@[2] == a * b + c,
        all_expressions(a, b, c)@[3] == a * (b + c),
        all_expressions(a, b, c)@[4] == (a + b) * c,
        all_expressions(a, b, c)@[5] == a + b + c,
{
}

/* helper modified by LLM (iteration 5): Fixed lemma_compare_expressions to use proper verification */
proof fn lemma_compare_expressions(a: int, b: int, c: int, result: int)
    requires
        valid_input(a, b, c),
        result == a * b * c || result == a + b * c || result == a * b + c || 
        result == a * (b + c) || result == (a + b) * c || result == a + b + c,
    ensures
        is_max_of_all_expressions(result, a, b, c),
{
    lemma_expression_equivalences(a, b, c);
    let exprs = all_expressions(a, b, c);
    assert(exprs.contains(result));
    
    let max_val = max_expression(a, b, c);
    assert(result <= max_val);
    assert(forall|j: int| 0 <= j < exprs.len() ==> max_val >= exprs[j]);
    assert(result <= max_val);
    assert(forall|j: int| 0 <= j < exprs.len() ==> result >= exprs[j] ==> result == exprs[j] || result > exprs[j]);
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
    /* code modified by LLM (iteration 5): Fixed variable declaration for max_val and added verification proof */
    proof {
        lemma_all_expressions_non_empty(a as int, b as int, c as int);
    }
    
    let expr1 = a * b * c;
    let expr2 = a + b * c;
    let expr3 = a * b + c;
    let expr4 = a * (b + c);
    let expr5 = (a + b) * c;
    let expr6 = a + b + c;
    
    let mut result_var = expr1;
    if expr2 > result_var { result_var = expr2; }
    if expr3 > result_var { result_var = expr3; }
    if expr4 > result_var { result_var = expr4; }
    if expr5 > result_var { result_var = expr5; }
    if expr6 > result_var { result_var = expr6; }
    
    proof {
        lemma_expression_equivalences(a as int, b as int, c as int);
        let max_val = max_expression(a as int, b as int, c as int);
        let exprs = all_expressions(a as int, b as int, c as int);
        lemma_max_property(exprs, max_val);
        lemma_compare_expressions(a as int, b as int, c as int, result_var as int);
        assert(result_var as int == max_val);
    }
    
    result_var
}
// </vc-code>


}

fn main() {}