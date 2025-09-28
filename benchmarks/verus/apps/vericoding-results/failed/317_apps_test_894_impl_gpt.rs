// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(x: int, y: int) -> bool {
    x != 0 && y != 0
}

spec fn valid_output(result: Seq<int>, x: int, y: int) -> bool {
    result.len() == 4 &&
    result[0] < result[2] &&
    (x * y > 0 && x < 0 ==> result =~= seq![x + y, 0, 0, x + y]) &&
    (x * y > 0 && x >= 0 ==> result =~= seq![0, x + y, x + y, 0]) &&
    (x * y <= 0 && x < 0 ==> result =~= seq![x - y, 0, 0, y - x]) &&
    (x * y <= 0 && x >= 0 ==> result =~= seq![0, y - x, x - y, 0])
}
// </vc-preamble>

// <vc-helpers>
proof fn both_pos_sum_pos(x: int, y: int)
    requires
        x > 0,
        y > 0,
    ensures
        x + y > 0,
{
}

proof fn both_neg_sum_neg(x: int, y: int)
    requires
        x < 0,
        y < 0,
    ensures
        x + y < 0,
{
}

proof fn neg_pos_diffs(x: int, y: int)
    requires
        x < 0,
        y > 0,
    ensures
        x - y < 0,
        y - x > 0,
{
}

proof fn pos_neg_diffs(x: int, y: int)
    requires
        x > 0,
        y < 0,
    ensures
        y - x < 0,
        x - y > 0,
{
}

fn mk4(a: i8, b: i8, c: i8, d: i8) -> (v: Vec<i8>)
    ensures
        v@ == seq![a, b, c, d],
{
    let mut v = Vec::new();
    v.push(a);
    v.push(b);
    v.push(c);
    v.push(d);
    v
}
// </vc-helpers>

// <vc-spec>
fn solve(x: i8, y: i8) -> (result: Vec<i8>)
    requires valid_input(x as int, y as int)
    ensures valid_output(result@.map(|i: int, v: i8| v as int), x as int, y as int)
// </vc-spec>
// <vc-code>
{
    let xi: int = x as int;
    let yi: int = y as int;
    if xi * yi > 0 {
        if xi < 0 {
            let s: i8 = x + y;
            let v = mk4(s, 0i8, 0i8, s);
            proof { both_neg_sum_neg(xi, yi); }
            v
        } else {
            let s: i8 = x + y;
            let v = mk4(0i8, s, s, 0i8);
            proof { both_pos_sum_pos(xi, yi); }
            v
        }
    } else {
        if xi < 0 {
            let a: i8 = x - y;
            let d: i8 = y - x;
            let v = mk4(a, 0i8, 0i8, d);
            proof { neg_pos_diffs(xi, yi); }
            v
        } else {
            let b: i8 = y - x;
            let c: i8 = x - y;
            let v = mk4(0i8, b, c, 0i8);
            proof { pos_neg_diffs(xi, yi); }
            v
        }
    }
}
// </vc-code>


}

fn main() {}