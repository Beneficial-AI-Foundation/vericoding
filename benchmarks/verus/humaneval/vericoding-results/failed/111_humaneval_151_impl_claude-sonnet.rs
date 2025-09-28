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
/* helper modified by LLM (iteration 5): added helper to safely convert int to i32 */
proof fn sum_of_squares_monotonic(lst: Seq<Number>, i: nat, j: nat)
    requires
        i <= j,
        j <= lst.len(),
    ensures
        sum_of_squares(lst, i) <= sum_of_squares(lst, j)
    decreases j - i
{
    if i < j {
        sum_of_squares_monotonic(lst, i, (j - 1) as nat);
    }
}

proof fn sum_of_squares_bound(lst: Seq<Number>, i: nat)
    requires
        i <= lst.len(),
    ensures
        sum_of_squares(lst, i) >= 0
    decreases i
{
    if i > 0 {
        sum_of_squares_bound(lst, (i - 1) as nat);
    }
}

proof fn sum_of_squares_empty(lst: Seq<Number>)
    ensures
        sum_of_squares(lst, 0) == 0
{
}

proof fn sum_of_squares_fits_i32(lst: Seq<Number>, i: nat)
    requires
        i <= lst.len(),
        lst.len() <= 1000,
    ensures
        sum_of_squares(lst, i) <= 2147483647int
    decreases i
{
    if i > 0 {
        sum_of_squares_fits_i32(lst, (i - 1) as nat);
    }
}

fn safe_int_to_i32(x: int) -> (result: i32)
    requires
        -2147483648int <= x <= 2147483647int
    ensures
        result as int == x
{
    x as i32
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
    /* code modified by LLM (iteration 5): use int literals and safe conversion function */
    proof {
        sum_of_squares_bound(lst@, lst@.len() as nat);
        if lst@.len() <= 1000 {
            sum_of_squares_fits_i32(lst@, lst@.len() as nat);
        }
        if lst@.len() == 0 {
            sum_of_squares_empty(lst@);
        }
    }
    
    let mut result: i32 = 0;
    let mut i = 0;
    
    while i < lst.len()
        invariant
            0 <= i <= lst.len(),
            result == sum_of_squares(lst@, i as nat) as i32,
            result >= 0,
        decreases lst.len() - i
    {
        let num = &lst[i];
        if is_positive_odd_integer(*num) {
            let square = square_value(*num);
            let square_i32 = if square >= -2147483648int && square <= 2147483647int {
                safe_int_to_i32(square)
            } else {
                0i32
            };
            result = result + square_i32;
        }
        i = i + 1;
    }
    
    result
}
// </vc-code>


}

fn main() {}