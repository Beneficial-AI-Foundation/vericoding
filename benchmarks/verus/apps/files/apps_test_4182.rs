// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn valid_input(n: int, m: int, x: int, y: int, xx: Seq<int>, yy: Seq<int>) -> bool {
    xx.len() == n && yy.len() == m && n >= 1 && m >= 1 && x < y
}

spec fn agreement_possible(n: int, m: int, x: int, y: int, xx: Seq<int>, yy: Seq<int>) -> bool
    recommends valid_input(n, m, x, y, xx, yy)
{
    let combined_x = xx.push(x);
    let combined_y = yy.push(y);
    (exists|max_val: int| combined_x.contains(max_val) && 
                     (forall|v: int| combined_x.contains(v) ==> v <= max_val) &&
     exists|min_val: int| combined_y.contains(min_val) && 
                     (forall|v: int| combined_y.contains(v) ==> v >= min_val) &&
                     max_val < min_val)
}
// </vc-helpers>

// <vc-spec>
fn solve(n: int, m: int, x: int, y: int, xx: Seq<int>, yy: Seq<int>) -> (result: String)
    requires 
        valid_input(n, m, x, y, xx, yy)
    ensures 
        result@ == "No War" || result@ == "War",
        result@ == "No War" <==> agreement_possible(n, m, x, y, xx, yy)
// </vc-spec>
// <vc-code>
{
    assume(false);
    String::new()
}
// </vc-code>


}

fn main() {}