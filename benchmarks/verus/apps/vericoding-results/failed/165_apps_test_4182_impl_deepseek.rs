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
/* helper modified by LLM (iteration 5): add decreases clause and maintain invariants */
fn exec_seq_max_exists(seq: &Vec<i8>) -> i8
    ensures
        exists|j: int| 0 <= j && j < seq.len() && seq@[j] == result,
        forall|k: int| 0 <= k && k < seq.len() ==> seq@[k] <= result,
{
    let mut max_val = seq[0];
    let mut i = 0;
    
    while i < seq.len()
        invariant
            i <= seq.len(),
            forall|j: int| 0 <= j && j < i ==> seq@[j] <= max_val,
            exists|j: int| 0 <= j && j < i && seq@[j] == max_val,
        decreases seq.len() - i
    {
        if seq[i] > max_val {
            max_val = seq[i];
        }
        i += 1;
    }
    max_val
}

/* helper modified by LLM (iteration 5): add decreases clause and maintain invariants */
fn exec_seq_min_exists(seq: &Vec<i8>) -> i8
    ensures
        exists|j: int| 0 <= j && j < seq.len() && seq@[j] == result,
        forall|k: int| 0 <= k && k < seq.len() ==> seq@[k] >= result,
{
    let mut min_val = seq[0];
    let mut i = 0;
    
    while i < seq.len()
        invariant
            i <= seq.len(),
            forall|j: int| 0 <= j && j < i ==> seq@[j] >= min_val,
            exists|j: int| 0 <= j && j < i && seq@[j] == min_val,
        decreases seq.len() - i
    {
        if seq[i] < min_val {
            min_val = seq[i];
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
/* code modified by LLM (iteration 5): return string literals without String::from */
{
    let mut max_x = exec_seq_max_exists(&xx);
    if x > max_x {
        max_x = x;
    }
    
    let mut min_y = exec_seq_min_exists(&yy);
    if y < min_y {
        min_y = y;
    }
    
    if max_x < min_y {
        "No War".to_string()
    } else {
        "War".to_string()
    }
}
// </vc-code>


}

fn main() {}