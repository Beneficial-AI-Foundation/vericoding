// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(l: Seq<int>) -> bool
{
    true
}

spec fn correct_output(l: Seq<int>, result: Seq<int>) -> bool
{
    result.len() == l.len() && 
    forall|i: int| 0 <= i < l.len() ==> result[i] == l[i] + 1
}
// </vc-preamble>

// <vc-helpers>
spec fn incr_i8(x: i8) -> i8 {
    (x as int + 1) as i8
}
// </vc-helpers>

// <vc-spec>
fn incr_list(l: Vec<i8>) -> (result: Vec<i8>)
    requires valid_input(l@.map(|i: int, x: i8| x as int))
    ensures correct_output(l@.map(|i: int, x: i8| x as int), result@.map(|i: int, x: i8| x as int))
// </vc-spec>
// <vc-code>
{
    let mut result: Vec<i8> = Vec::new();
    let n: usize = l.len();
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
        decreases n - i
    {
        let x: i8 = l[i];
        let y: i8 = ((x as int) + 1) as i8;
        result.push(y);
        i += 1;
    }
    result
}
// </vc-code>


}

fn main() {}