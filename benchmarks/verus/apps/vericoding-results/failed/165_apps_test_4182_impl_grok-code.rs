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
/* helper modified by LLM (iteration 5): No modifications needed, compilation error in code section */
exec fn find_max_vec(v: &Vec<i8>) -> (result: int)
    requires
        v.len() >= 1,
    ensures
        forall|i: int| 0 <= i < v.len() ==> v[i] as int <= result,
        exists|i: int| 0 <= i < v.len() && v[i] as int == result,
{
    let mut max: int = v[0] as int;
    let mut i: int = 1;
    while i < (v.len() as int)
        invariant
            0 <= i <= v.len(),
            forall|j: int| 0 <= j < i ==> v[j as int] as int <= max,
            exists|j: int| 0 <= j < i && v[j as int] as int == max,
        decreases v.len() - i
    {
        if (v[i as usize] as int) > max {
            max = v[i as usize] as int;
        }
        i = i + 1;
    }
    max
}

exec fn find_min_vec(v: &Vec<i8>) -> (result: int)
    requires
        v.len() >= 1,
    ensures
        forall|i: int| 0 <= i < v.len() ==> v[i] as int >= result,
        exists|i: int| 0 <= i < v.len() && v[i] as int == result,
{
    let mut min: int = v[0] as int;
    let mut i: int = 1;
    while i < (v.len() as int)
        invariant
            0 <= i <= v.len(),
            forall|j: int| 0 <= j < i ==> v[j as int] as int >= min,
            exists|j: int| 0 <= j < i && v[j as int] as int == min,
        decreases v.len() - i
    {
        if (v[i as usize] as int) < min {
            min = v[i as usize] as int;
        }
        i = i + 1;
    }
    min
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
/* code modified by LLM (iteration 5): Added parentheses around if conditions to fix compilation error */
{
    let xx_max: int = find_max_vec(&xx);
    let combined_xx_max: int = if (x as int > xx_max) { x as int } else { xx_max };
    let yy_min: int = find_min_vec(&yy);
    let combined_yy_min: int = if (y as int < yy_min) { y as int } else { yy_min };
    if combined_xx_max < combined_yy_min {
        "No War".to_string()
    } else {
        "War".to_string()
    }
}
// </vc-code>


}

fn main() {}