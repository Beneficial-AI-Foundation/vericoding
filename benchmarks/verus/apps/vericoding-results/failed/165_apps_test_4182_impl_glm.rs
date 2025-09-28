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
/* helper modified by LLM (iteration 5): added decreases clause for termination */
fn vec_max(v: &Vec<i8>) -> (max_val: i8)
    requires v.len() > 0,
    ensures
        forall|i: int| 0 <= i < v.len() ==> v@[i] <= max_val,
        exists|i: int| 0 <= i < v.len() && v@[i] == max_val,
{
    let mut max_val = v[0];
    let mut i = 1;
    while i < v.len()
        invariant
            1 <= i <= v.len(),
            forall|j: int| 0 <= j < i ==> v@[j] <= max_val,
            exists|j: int| 0 <= j < i && v@[j] == max_val,
        decreases v.len() - i,
    {
        if v[i] > max_val {
            max_val = v[i];
        }
        i += 1;
    }
    max_val
}

/* helper modified by LLM (iteration 5): added decreases clause for termination */
fn vec_min(v: &Vec<i8>) -> (min_val: i8)
    requires v.len() > 0,
    ensures
        forall|i: int| 0 <= i < v.len() ==> v@[i] >= min_val,
        exists|i: int| 0 <= i < v.len() && v@[i] == min_val,
{
    let mut min_val = v[0];
    let mut i = 1;
    while i < v.len()
        invariant
            1 <= i <= v.len(),
            forall|j: int| 0 <= j < i ==> v@[j] >= min_val,
            exists|j: int| 0 <= j < i && v@[j] == min_val,
        decreases v.len() - i,
    {
        if v[i] < min_val {
            min_val = v[i];
        }
        i += 1;
    }
    min_val
}
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
    /* code modified by LLM (iteration 4): fixed return type from &str to String */
    let max_xx = vec_max(&xx);
    let max_x = if max_xx > x { max_xx } else { x };
    let min_yy = vec_min(&yy);
    let min_y = if min_yy < y { min_yy } else { y };
    if max_x < min_y {
        \"No War\".to_string()
    } else {
        \"War\".to_string()
    }
}
// </vc-code>


}

fn main() {}