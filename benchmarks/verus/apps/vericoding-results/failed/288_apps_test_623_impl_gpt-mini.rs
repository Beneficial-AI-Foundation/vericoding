// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn count_valid_minutes(a: int, b: int) -> int
    recommends a >= 0 && b >= 0
    decreases a + b
{
    if a <= 0 || b <= 0 {
        0
    } else if a == 1 && b == 1 {
        0
    } else {
        (if a > 1 || b > 1 { 1 as int } else { 0 as int }) + 
        count_valid_minutes(
            if a < b { a + 1 } else { a - 2 }, 
            if a < b { b - 2 } else { b + 1 }
        )
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): spec helper exec_count mirrors count_valid_minutes */
spec fn exec_count(a: int, b: int) -> int
    requires
        a >= 0 && b >= 0,
    ensures
        result >= 0,
    decreases
        a + b
{
    if a <= 0 || b <= 0 {
        0
    } else if a == 1 && b == 1 {
        0
    } else {
        let add = if a > 1 || b > 1 { 1 } else { 0 };
        let (na, nb) = if a < b { (a + 1, b - 2) } else { (a - 2, b + 1) };
        add + exec_count(na, nb)
    }
}

/* helper modified by LLM (iteration 5): lemma proving exec_count equals count_valid_minutes by induction */
proof fn lemma_exec_eq_spec(a: int, b: int)
    requires
        a >= 0 && b >= 0,
    ensures
        exec_count(a, b) == count_valid_minutes(a, b),
    decreases
        a + b
{
    if a <= 0 || b <= 0 {
        assert(exec_count(a, b) == 0);
        assert(count_valid_minutes(a, b) == 0);
    } else if a == 1 && b == 1 {
        assert(exec_count(a, b) == 0);
        assert(count_valid_minutes(a, b) == 0);
    } else {
        let add = if a > 1 || b > 1 { 1 } else { 0 };
        let (na, nb) = if a < b { (a + 1, b - 2) } else { (a - 2, b + 1) };
        proof {
            lemma_exec_eq_spec(na, nb);
            assert(exec_count(na, nb) == count_valid_minutes(na, nb));
            assert(exec_count(a, b) == add + exec_count(na, nb));
            assert(count_valid_minutes(a, b) == add + count_valid_minutes(na, nb));
        }
        assert(exec_count(a, b) == count_valid_minutes(a, b));
    }
}

// </vc-helpers>

// <vc-spec>
fn solve(a1: i8, a2: i8) -> (result: i8)
    requires 
        a1 >= 1 && a2 >= 1,
    ensures 
        result >= 0,
        result as int == count_valid_minutes(a1 as int, a2 as int),
        (a1 == 1 && a2 == 1) ==> result == 0,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): compute exec_count, prove equality with spec, assign to result and return */
    let res_int: int = exec_count(a1 as int, a2 as int);
    proof {
        lemma_exec_eq_spec(a1 as int, a2 as int);
        assert(res_int == count_valid_minutes(a1 as int, a2 as int));
        assert(res_int >= 0);
    }
    let result: i8 = res_int as i8;
    result
}
// </vc-code>


}

fn main() {}