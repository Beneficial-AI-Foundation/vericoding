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
fn is_positive_odd_integer_exec(n: &Number) -> (is_pos_odd: bool)
    ensures
        is_pos_odd == is_positive_odd_integer(*n),
{
    match n {
        Number::Int(i) => *i > 0 && *i % 2 == 1,
        Number::Real(r) => *r > 0 && *r % 2 == 1,
    }
}

fn square_value_exec(n: &Number) -> (sq: int)
    ensures
        sq == square_value(*n),
        sq >= 0,
{
    let val = match n {
        Number::Int(i) => *i,
        Number::Real(r) => *r,
    };
    val * val
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
    let mut sum: int = 0;
    let mut i: usize = 0;

    while i < lst.len()
        invariant
            i <= lst.len(),
            sum >= 0,
            sum == sum_of_squares(lst@, i as nat),
        decreases lst.len() - i
    {
        let current_num = &lst[i];

        if is_positive_odd_integer_exec(current_num) {
            let squared = square_value_exec(current_num);
            sum = sum + squared;
        }
        
        i = i + 1;
    }
    
    sum as i32
}
// </vc-code>


}

fn main() {}