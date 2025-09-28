// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(n: int, m: int, x: int, y: int, xx: Seq<int>, yy: Seq<int>) -> bool {
    xx.len() == n && yy.len() == m && n >= 1 && m >= 1 && x < y
}

spec fn agreement_possible(n: int, m: int, x: int, y: int, xx: Seq<int>, yy: Seq<int>) -> bool 
    recommends valid_input(n, m, x, y, xx, yy)
{
    let combined_x = xx.push(x);
    let combined_y = yy.push(y);
    exists|max_val: int| combined_x.contains(max_val) && 
                         (forall|v: int| combined_x.contains(v) ==> v <= max_val) &&
    exists|min_val: int| combined_y.contains(min_val) && 
                         (forall|v: int| combined_y.contains(v) ==> v >= min_val) &&
                         max_val < min_val
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): map Vec<i8> to Seq<int> */
spec fn vec_map(xs: Vec<i8>) -> Seq<int> { xs@.map(|_i: int, v: i8| v as int) }

/* helper modified by LLM (iteration 3): append element to mapped sequence */
spec fn combined_with(xs: Vec<i8>, a: i8) -> Seq<int> { vec_map(xs).push(a as int) }
// </vc-helpers>

// <vc-spec>
fn solve(n: i8, m: i8, x: i8, y: i8, xx: Vec<i8>, yy: Vec<i8>) -> (result: String)
    requires 
        valid_input(n as int, m as int, x as int, y as int, xx@.map(|_i: int, v: i8| v as int), yy@.map(|_i: int, v: i8| v as int)),
    ensures 
        result@ == seq!['N','o',' ','W','a','r'] || result@ == seq!['W','a','r'],
        (result@ == seq!['N','o',' ','W','a','r']) == agreement_possible(n as int, m as int, x as int, y as int, xx@.map(|_i: int, v: i8| v as int), yy@.map(|_i: int, v: i8| v as int)),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): compute max of xx and min of yy and decide result */
    let mut i: usize = 0usize;
    let mut cur_max: i8 = x;
    while i < xx.len()
        invariant
            0 <= i as int && i as int <= xx.len() as int,
            (forall|k: int| 0 <= k && k < i as int ==> vec_map(xx)@[k] <= cur_max as int),
            cur_max as int == x as int || (exists|k: int| 0 <= k && k < i as int && vec_map(xx)@[k] == cur_max as int),
        decreases (xx.len() as int - i as int)
    {
        let v: i8 = xx.index(i);
        if v > cur_max {
            cur_max = v;
        }
        i = i + 1;
    }

    let mut j: usize = 0usize;
    let mut cur_min: i8 = y;
    while j < yy.len()
        invariant
            0 <= j as int && j as int <= yy.len() as int,
            (forall|k: int| 0 <= k && k < j as int ==> vec_map(yy)@[k] >= cur_min as int),
            cur_min as int == y as int || (exists|k: int| 0 <= k && k < j as int && vec_map(yy)@[k] == cur_min as int),
        decreases (yy.len() as int - j as int)
    {
        let v: i8 = yy.index(j);
        if v < cur_min {
            cur_min = v;
        }
        j = j + 1;
    }

    let combined_x = combined_with(xx, x);
    let combined_y = combined_with(yy, y);

    proof {
        if cur_max as int == x as int {
            assert(combined_x.contains(cur_max as int));
        } else {
            assert(exists|k: int| 0 <= k && k < xx.len() as int && vec_map(xx)@[k] == cur_max as int);
            assert(combined_x.contains(cur_max as int));
        }

        assert(forall|v: int| combined_x.contains(v) ==> v <= cur_max as int);

        if cur_min as int == y as int {
            assert(combined_y.contains(cur_min as int));
        } else {
            assert(exists|k: int| 0 <= k && k < yy.len() as int && vec_map(yy)@[k] == cur_min as int);
            assert(combined_y.contains(cur_min as int));
        }

        assert(forall|v: int| combined_y.contains(v) ==> v >= cur_min as int);
    }

    if cur_max < cur_min {
        let res = String::from_str("No War");
        proof {
            assert(exists|max_val: int|
                combined_x.contains(max_val) && (forall|v: int| combined_x.contains(v) ==> v <= max_val) &&
                exists|min_val: int| combined_y.contains(min_val) && (forall|v: int| combined_y.contains(v) ==> v >= min_val) && max_val < min_val
            );
        }
        res
    } else {
        let res = String::from_str("War");
        proof {
            assert(!(exists|max_val: int|
                combined_x.contains(max_val) && (forall|v: int| combined_x.contains(v) ==> v <= max_val) &&
                exists|min_val: int| combined_y.contains(min_val) && (forall|v: int| combined_y.contains(v) ==> v >= min_val) && max_val < min_val
            ));
        }
        res
    }
}

// </vc-code>


}

fn main() {}