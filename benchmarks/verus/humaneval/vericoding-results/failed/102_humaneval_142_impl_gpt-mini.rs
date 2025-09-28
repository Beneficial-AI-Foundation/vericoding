// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn transform_element(value: int, index: int) -> int
{
    if index % 3 == 0 { 
        value * value
    } else if index % 4 == 0 { 
        value * value * value
    } else { 
        value
    }
}

spec fn sum_partial(lst: Seq<int>, n: int) -> int
    decreases n
    when 0 <= n <= lst.len()
{
    if n == 0 { 
        0
    } else { 
        sum_partial(lst, n-1) + transform_element(lst[n-1], n-1)
    }
}

spec fn sum_transformed(lst: Seq<int>) -> int
{
    sum_partial(lst, lst.len() as int)
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): convert Seq<i8> to Seq<int> */
spec fn seq_to_int(s: Seq<i8>) -> Seq<int> {
    s.map(|i, x: i8| x as int)
}
// </vc-helpers>

// <vc-spec>
fn sum_squares(lst: Vec<i8>) -> (result: i8)
    ensures result as int == sum_transformed(seq_to_int(lst@))
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): compute runtime sum and maintain ghost acc via idx var */
    let ghost s: Seq<int> = seq_to_int(lst@);
    let ghost mut acc: int = 0;
    let mut res: i64 = 0;
    let mut i: usize = 0;
    while i < lst.len()
        invariant
            0 <= i as int,
            i as int <= lst.len() as int,
            acc == sum_partial(s, i as int),
            acc == res as int,
        decreases lst.len() - i
    {
        let v: i64 = lst[i] as i64;
        if i % 3 == 0 {
            res = res + v * v;
        } else if i % 4 == 0 {
            res = res + v * v * v;
        } else {
            res = res + v;
        }
        ghost {
            let idx: int = i as int;
            acc = acc + transform_element(s@[idx], idx);
        }
        i = i + 1;
    }
    proof {
        assert(!(i < lst.len()));
        assert(i >= lst.len());
        assert(i == lst.len());
        assert(acc == sum_partial(s, i as int));
        assert(acc == sum_transformed(s));
    }
    res as i8
}
// </vc-code>


}

fn main() {}