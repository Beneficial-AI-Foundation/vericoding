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

// </vc-helpers>

// <vc-spec>
fn double_the_difference(lst: Vec<Number>) -> (result: i32)
    ensures 
        result >= 0,
        result == sum_of_squares(lst@, lst@.len()) as i32,
        lst@.len() == 0 ==> result == 0
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Changed the loop variable 'i' type from 'int' to 'usize' to align with array indexing and avoid unnecessary casting and compilation errors. Updated loop invariant and termination measure accordingly. */
{
    let mut total_sum: int = 0;
    let mut i: usize = 0;
    let len_usize = lst.len();

    while i < len_usize
        invariant
            0 <= i,
            i <= len_usize,
            total_sum == sum_of_squares(lst@, i as nat),
        decreases len_usize - i
    {

        let current_num_ref = &lst[i];
        if is_positive_odd_integer(*current_num_ref) {
            let sq_val = square_value(*current_num_ref);
            total_sum = total_sum + sq_val;
        }
        i = i + 1;
    }
    
    proof {
        assert(total_sum == sum_of_squares(lst@, lst.len() as nat));
    }

    total_sum as i32
}
// </vc-code>


}

fn main() {}