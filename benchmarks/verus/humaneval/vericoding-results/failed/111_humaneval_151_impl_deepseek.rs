// <vc-preamble>
use vstd::prelude::*;

verus! {

enum Number {
    Int(int),
    Real(int), /* Using int to represent real since Verus doesn't have native real type */
}

spec fn is_integer(r: int) -> bool {
    true /* Since we're using int to represent real, this is always true */
}

spec fn is_positive_odd_integer(n: Number) -> bool {
    match n {
        Number::Int(i) => i > 0 && i % 2 == 1,
        Number::Real(r) => is_integer(r) && r > 0 && r % 2 == 1,
    }
}

spec fn square_value(n: Number) -> int {
    match n {
        Number::Int(i) => i * i,
        Number::Real(r) => r * r,
    }
}

spec fn sum_of_squares(lst: Seq<Number>, i: nat) -> int
    decreases i
{
    if i == 0 {
        0
    } else if is_positive_odd_integer(lst[(i - 1) as int]) {
        square_value(lst[(i - 1) as int]) + sum_of_squares(lst, (i - 1) as nat)
    } else {
        sum_of_squares(lst, (i - 1) as nat)
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed type conversion issues and simplified helper functions to work with int types */
fn helper_square_value(n: Number) -> (res: int)
    ensures
        res == square_value(n),
{
    match n {
        Number::Int(i) => i * i,
        Number::Real(r) => r * r,
    }
}

proof fn lemma_sum_of_squares_boundary(lst: Seq<Number>, i: nat)
    ensures
        i == 0 ==> sum_of_squares(lst, i) == 0,
{
    if i == 0 {
        assert(sum_of_squares(lst, 0) == 0);
    }
}

fn helper_is_positive_odd(i: int) -> (res: bool)
    ensures
        res == (i > 0 && i % 2 == 1),
{
    i > 0 && i % 2 == 1
}
// </vc-helpers>

// <vc-spec>
fn double_the_difference(lst: Vec<Number>) -> (result: i32)
    ensures 
        result >= 0,
        result == sum_of_squares(lst@, lst@.len()) as i32,
        lst@.len() == 0 ==> result == 0
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed type casting issues, using int arithmetic instead of i32 */
    let mut total: int = 0;
    let mut idx: usize = 0;
    
    while idx < lst.len()
        invariant
            total >= 0,
            idx <= lst.len(),
            total == sum_of_squares(lst@, idx as nat),
    {
        let item = lst[idx];
        match item {
            Number::Int(i) => {
                if helper_is_positive_odd(i) {
                    let square_val = helper_square_value(item);
                    total = total + square_val;
                }
            },
            Number::Real(r) => {
                if helper_is_positive_odd(r) {
                    let square_val = helper_square_value(item);
                    total = total + square_val;
                }
            },
        }
        idx += 1;
    }
    
    total as i32
}
// </vc-code>


}

fn main() {}