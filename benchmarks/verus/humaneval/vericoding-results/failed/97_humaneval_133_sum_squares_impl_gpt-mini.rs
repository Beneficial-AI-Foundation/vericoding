// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn sum(s: Seq<int>) -> int
    decreases s.len()
{
    if s.len() == 0 { 0 } else { s[0] + sum(s.subrange(1, s.len() as int)) }
}

spec fn ceil(f: int) -> int {
    f + 1
}

spec fn square_seq(lst: Seq<int>) -> Seq<int> {
    Seq::new(lst.len(), |i: int| ceil(lst[i]) * ceil(lst[i]))
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): convert i8 to int */
spec fn i8_to_int(x: i8) -> int {
    x as int
}

/* helper modified by LLM (iteration 5): square of ceiled value */
spec fn square_ceiled_of_i8(x: i8) -> int {
    let xi: int = x as int;
    ceil(xi) * ceil(xi)
}
// </vc-helpers>

// <vc-spec>
fn sum_squares(lst: Vec<i8>) -> (r: i8)
    ensures r as int == sum(square_seq(lst@.map(|i: int, x: i8| x as int)))
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): compute sum using ghost sequence and ghost accumulator */
    let n: usize = lst.len();
    let n_int: int = n as int;
    let ghost s: Seq<int> = lst@.map(|k: int, x: i8| x as int);
    let mut i: int = 0;
    let ghost mut acc: int = 0;
    while i < n_int
        invariant
            0 <= i <= n_int,
            acc == sum(square_seq(s.subrange(0, i))),
        decreases n_int - i
    {
        ghost {
            let v: int = s@[i];
            acc = acc + ceil(v) * ceil(v);
        }
        i = i + 1;
    }
    let r: i8 = #[verifier::truncate] acc as i8;
    r
}
// </vc-code>


}

fn main() {}