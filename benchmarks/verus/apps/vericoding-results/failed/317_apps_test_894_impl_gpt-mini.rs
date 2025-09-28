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
/* helper modified by LLM (iteration 2): prove that Vec<i8> maps to a valid Seq<int> output */
proof fn helpers_prove_valid_output(res: &Vec<i8>, x: i8, y: i8)
    requires
        res.len() == 4,
        res@.map(|i: int, v: i8| v as int)@[0] < res@.map(|i: int, v: i8| v as int)@[2],
        (x as int * y as int > 0 && x as int < 0 ==> res@.map(|i: int, v: i8| v as int) =~= seq![x as int + y as int, 0, 0, x as int + y as int]),
        (x as int * y as int > 0 && x as int >= 0 ==> res@.map(|i: int, v: i8| v as int) =~= seq![0, x as int + y as int, x as int + y as int, 0]),
        (x as int * y as int <= 0 && x as int < 0 ==> res@.map(|i: int, v: i8| v as int) =~= seq![x as int - y as int, 0, 0, y as int - x as int]),
        (x as int * y as int <= 0 && x as int >= 0 ==> res@.map(|i: int, v: i8| v as int) =~= seq![0, y as int - x as int, x as int - y as int, 0]),
    ensures
        valid_output(res@.map(|i: int, v: i8| v as int), x as int, y as int),
{
    proof {
        // The preconditions already match the conjuncts of valid_output for the mapped sequence,
        // so we just assert them to construct the postcondition.
        assert(res.len() == 4);
        assert(res@.map(|i: int, v: i8| v as int)@[0] < res@.map(|i: int, v: i8| v as int)@[2]);
        assert((x as int * y as int > 0 && x as int < 0 ==> res@.map(|i: int, v: i8| v as int) =~= seq![x as int + y as int, 0, 0, x as int + y as int]));
        assert((x as int * y as int > 0 && x as int >= 0 ==> res@.map(|i: int, v: i8| v as int) =~= seq![0, x as int + y as int, x as int + y as int, 0]));
        assert((x as int * y as int <= 0 && x as int < 0 ==> res@.map(|i: int, v: i8| v as int) =~= seq![x as int - y as int, 0, 0, y as int - x as int]));
        assert((x as int * y as int <= 0 && x as int >= 0 ==> res@.map(|i: int, v: i8| v as int) =~= seq![0, y as int - x as int, x as int - y as int, 0]));
    }
}

// </vc-helpers>

// <vc-spec>
fn solve(x: i8, y: i8) -> (result: Vec<i8>)
    requires valid_input(x as int, y as int)
    ensures valid_output(result@.map(|i: int, v: i8| v as int), x as int, y as int)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): construct result Vec<i8> according to signed cases and prove validity */
{
    let xi: int = x as int;
    let yi: int = y as int;

    let mut e0: i8 = 0i8;
    let mut e1: i8 = 0i8;
    let mut e2: i8 = 0i8;
    let mut e3: i8 = 0i8;

    if xi * yi > 0 {
        if xi < 0 {
            let v: i8 = (xi + yi) as i8;
            e0 = v;
            e3 = v;
        } else {
            let v: i8 = (xi + yi) as i8;
            e1 = v;
            e2 = v;
        }
    } else {
        if xi < 0 {
            let a: i8 = (xi - yi) as i8;
            let b: i8 = (yi - xi) as i8;
            e0 = a;
            e3 = b;
        } else {
            let a: i8 = (yi - xi) as i8;
            let b: i8 = (xi - yi) as i8;
            e1 = a;
            e2 = b;
        }
    }

    let res: Vec<i8> = Vec::from_slice(&[e0, e1, e2, e3]);

    proof {
        helpers_prove_valid_output(&res, x, y);
    }

    res
}

// </vc-code>


}

fn main() {}