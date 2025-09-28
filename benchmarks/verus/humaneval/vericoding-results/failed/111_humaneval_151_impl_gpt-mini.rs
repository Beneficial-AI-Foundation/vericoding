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
/* helper modified by LLM (iteration 5): fix seq indexing and relation between sum_of_squares for consecutive indices */
fn seq_step(lst: Seq<Number>, i: nat)
    requires
        i < lst.len(),
    ensures
        if is_positive_odd_integer(lst[i as int]) {
            sum_of_squares(lst, i + 1) == square_value(lst[i as int]) + sum_of_squares(lst, i)
        } else {
            sum_of_squares(lst, i + 1) == sum_of_squares(lst, i)
        },
{
    proof {
        assert(sum_of_squares(lst, i + 1) ==
            if is_positive_odd_integer(lst[i as int]) {
                square_value(lst[i as int]) + sum_of_squares(lst, i)
            } else {
                sum_of_squares(lst, i)
            });
    }
}

/* helper modified by LLM (iteration 5): prove square_value matches runtime enum variants */
fn square_matches_runtime(n: Number)
    ensures
        match n {
            Number::Int(i) => square_value(n) == i * i,
            Number::Real(r) => square_value(n) == r * r,
        },
{
    proof {
        match n {
            Number::Int(i) => {
                assert(square_value(Number::Int(i)) == i * i);
            }
            Number::Real(r) => {
                assert(square_value(Number::Real(r)) == r * r);
            }
        }
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
/* code modified by LLM (iteration 5): use int literals via .into(), maintain acc as int and convert at end */
{
    let mut idx: usize = 0;
    let mut acc: int = 0.into();
    while idx < lst.len()
        invariant
            acc >= 0.into(),
            acc == sum_of_squares(lst@, idx as nat),
        decreases
            lst.len() - idx
    {
        match lst.get(idx) {
            Some(n_ref) => {
                match n_ref {
                    &Number::Int(v) => {
                        if v > 0.into() && v % 2.into() == 1.into() {
                            proof {
                                seq_step(lst@, idx as nat);
                                square_matches_runtime(Number::Int(v));
                            }
                            acc = acc + v * v;
                        }
                    }
                    &Number::Real(r) => {
                        if r > 0.into() && r % 2.into() == 1.into() {
                            proof {
                                seq_step(lst@, idx as nat);
                                square_matches_runtime(Number::Real(r));
                            }
                            acc = acc + r * r;
                        }
                    }
                }
            }
            None => {}
        }
        idx = idx + 1;
    }
    acc.into()
}
// </vc-code>


}

fn main() {}