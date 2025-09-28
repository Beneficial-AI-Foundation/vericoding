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
proof fn sum_append_single(s: Seq<int>, x: int)
    ensures sum(s.push(x)) == sum(s) + x
    decreases s.len()
{
    if s.len() == 0 {
        assert(s.push(x) =~= seq![x]);
    } else {
        let tail = s.subrange(1, s.len() as int);
        assert(s.push(x) =~= seq![s[0]].add(tail.push(x)));
        sum_append_single(tail, x);
    }
}
// </vc-helpers>

// <vc-spec>
fn sum_squares(lst: Vec<i8>) -> (r: i8)
    ensures r as int == sum(square_seq(lst@.map(|i: int, x: i8| x as int)))
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): use ghost variable for int conversion */
    let mut result: i8 = 0;
    let mut i = 0;
    while i < lst.len()
        invariant
            0 <= i <= lst.len(),
            result as int == sum(square_seq(lst@.subrange(0, i as int).map(|j: int, x: i8| x as int))),
        decreases lst.len() - i
    {
        let ghost val = lst@[i as int];
        let ceil_val = val + 1;
        let square = ceil_val * ceil_val;
        result = result + (square as i8);
        i = i + 1;
    }
    result
}
// </vc-code>


}

fn main() {}