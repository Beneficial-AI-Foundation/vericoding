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
lemma sum_of_squares_step(s: Seq<Number>, i: nat)
    requires i < s.len()
    ensures 
        sum_of_squares(s, i+1) == 
            if is_positive_odd_integer(s@[i]) then square_value(s@[i]) + sum_of_squares(s, i) 
            else sum_of_squares(s, i)
{
    if i == 0 {
        let s0 = s@[0];
        let cond = is_positive_odd_integer(s0);
        assert(sum_of_squares(s, 1) == 
            if cond { square_value(s0) } else { 0 });
        assert(if cond { square_value(s0) } else { 0 } == 
            if cond { square_value(s0) + sum_of_squares(s,0) } else { sum_of_squares(s,0) });
    } else {
        assert(sum_of_squares(s, i+1) == 
            if is_positive_odd_integer(s@[i]) then square_value(s@[i]) + sum_of_squares(s, i) 
            else sum_of_squares(s, i));
    }
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
    let mut i: nat = 0;
    while i < lst.len()
        invariant 
            0 <= i <= lst.len(),
            sum == sum_of_squares(lst@, i),
            sum >= 0,
        decreases lst.len() - i
    {
        let current = lst[i];
        let cond = is_positive_odd_integer(current);
        let old_sum = sum;
        if cond {
            sum = old_sum + square_value(current);
        } else {
            sum = old_sum;
        }
        proof {
            sum_of_squares_step(lst@, i);
        }
        i = i + 1;
    }
    sum as i32
}
// </vc-code>


}

fn main() {}