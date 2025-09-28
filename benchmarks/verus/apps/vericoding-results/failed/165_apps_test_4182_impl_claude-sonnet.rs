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
/* helper modified by LLM (iteration 5): fix nat type mismatches and sequence indexing */
spec fn seq_max(s: Seq<int>) -> int
    requires s.len() > 0
{
    if s.len() == 1nat {
        s@[0]
    } else {
        let rest_max = seq_max(s.drop_last());
        if s.last() > rest_max { s.last() } else { rest_max }
    }
}

spec fn seq_min(s: Seq<int>) -> int
    requires s.len() > 0
{
    if s.len() == 1nat {
        s@[0]
    } else {
        let rest_min = seq_min(s.drop_last());
        if s.last() < rest_min { s.last() } else { rest_min }
    }
}

proof fn lemma_max_properties(s: Seq<int>)
    requires s.len() > 0
    ensures
        s.contains(seq_max(s)),
        forall|v: int| s.contains(v) ==> v <= seq_max(s)
{
    if s.len() == 1nat {
    } else {
        lemma_max_properties(s.drop_last());
    }
}

proof fn lemma_min_properties(s: Seq<int>)
    requires s.len() > 0
    ensures
        s.contains(seq_min(s)),
        forall|v: int| s.contains(v) ==> v >= seq_min(s)
{
    if s.len() == 1nat {
    } else {
        lemma_min_properties(s.drop_last());
    }
}

fn compute_max(v: Vec<i8>) -> (result: i8)
    requires v.len() > 0
    ensures result as int == seq_max(v@.map(|_i: int, val: i8| val as int))
{
    let mut max_val = v[0];
    let mut i = 1;
    while i < v.len()
        invariant
            0 < i <= v.len(),
            max_val as int == seq_max(v@.subrange(0, i as int).map(|_j: int, val: i8| val as int))
    {
        if v[i] > max_val {
            max_val = v[i];
        }
        i += 1;
    }
    max_val
}

fn compute_min(v: Vec<i8>) -> (result: i8)
    requires v.len() > 0
    ensures result as int == seq_min(v@.map(|_i: int, val: i8| val as int))
{
    let mut min_val = v[0];
    let mut i = 1;
    while i < v.len()
        invariant
            0 < i <= v.len(),
            min_val as int == seq_min(v@.subrange(0, i as int).map(|_j: int, val: i8| val as int))
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
    /* code modified by LLM (iteration 5): fix compilation errors with proper Verus sequence operations */
    let ghost xx_seq = xx@.map(|_i: int, v: i8| v as int);
    let ghost yy_seq = yy@.map(|_i: int, v: i8| v as int);
    let ghost combined_x = xx_seq.push(x as int);
    let ghost combined_y = yy_seq.push(y as int);
    
    let mut xx_with_x = xx.clone();
    xx_with_x.push(x);
    let mut yy_with_y = yy.clone();
    yy_with_y.push(y);
    
    let max_x = compute_max(xx_with_x);
    let min_y = compute_min(yy_with_y);
    
    proof {
        lemma_max_properties(combined_x);
        lemma_min_properties(combined_y);
    }
    
    if max_x < min_y {
        String::from_str("No War")
    } else {
        String::from_str("War")
    }
}
// </vc-code>


}

fn main() {}