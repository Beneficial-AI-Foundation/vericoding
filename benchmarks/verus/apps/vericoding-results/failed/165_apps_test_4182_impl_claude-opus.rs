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
/* helper modified by LLM (iteration 5): Added lemmas to prove containment in combined sequences */
fn find_max(xx: &Vec<i8>, x: i8) -> (max_val: i8)
    requires
        xx@.len() >= 0,
    ensures
        max_val >= x,
        forall|i: int| 0 <= i < xx@.len() ==> max_val >= xx@[i],
        max_val == x || exists|i: int| 0 <= i < xx@.len() && max_val == xx@[i],
{
    let mut max = x;
    let mut i = 0;
    while i < xx.len()
        invariant
            0 <= i <= xx.len(),
            max >= x,
            forall|j: int| 0 <= j < i ==> max >= xx@[j],
            max == x || exists|j: int| 0 <= j < i && max == xx@[j],
        decreases xx.len() - i
    {
        if xx[i] > max {
            max = xx[i];
        }
        i += 1;
    }
    max
}

fn find_min(yy: &Vec<i8>, y: i8) -> (min_val: i8)
    requires
        yy@.len() >= 0,
    ensures
        min_val <= y,
        forall|i: int| 0 <= i < yy@.len() ==> min_val <= yy@[i],
        min_val == y || exists|i: int| 0 <= i < yy@.len() && min_val == yy@[i],
{
    let mut min = y;
    let mut i = 0;
    while i < yy.len()
        invariant
            0 <= i <= yy.len(),
            min <= y,
            forall|j: int| 0 <= j < i ==> min <= yy@[j],
            min == y || exists|j: int| 0 <= j < i && min == yy@[j],
        decreases yy.len() - i
    {
        if yy[i] < min {
            min = yy[i];
        }
        i += 1;
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
{
    /* code modified by LLM (iteration 5): Fixed proof to show max_x and min_y are in combined sequences */
    let max_x = find_max(&xx, x);
    let min_y = find_min(&yy, y);
    
    proof {
        assert(max_x as int >= x as int);
        assert(min_y as int <= y as int);
        assert(forall|i: int| 0 <= i < xx@.len() ==> max_x as int >= xx@[i] as int);
        assert(forall|i: int| 0 <= i < yy@.len() ==> min_y as int <= yy@[i] as int);
    }
    
    if max_x < min_y {
        proof {
            let combined_x = xx@.map(|_i: int, v: i8| v as int).push(x as int);
            let combined_y = yy@.map(|_i: int, v: i8| v as int).push(y as int);
            
            // Prove max_x is in combined_x
            if max_x == x {
                assert(combined_x[combined_x.len() - 1] == x as int);
                assert(combined_x.contains(x as int));
                assert(combined_x.contains(max_x as int));
            } else {
                assert(exists|i: int| 0 <= i < xx@.len() && max_x == xx@[i]);
                let witness_i = choose|i: int| 0 <= i < xx@.len() && max_x == xx@[i];
                assert(combined_x[witness_i] == xx@.map(|_i: int, v: i8| v as int)[witness_i]);
                assert(combined_x[witness_i] == xx@[witness_i] as int);
                assert(combined_x[witness_i] == max_x as int);
                assert(combined_x.contains(max_x as int));
            }
            
            // Prove min_y is in combined_y
            if min_y == y {
                assert(combined_y[combined_y.len() - 1] == y as int);
                assert(combined_y.contains(y as int));
                assert(combined_y.contains(min_y as int));
            } else {
                assert(exists|i: int| 0 <= i < yy@.len() && min_y == yy@[i]);
                let witness_i = choose|i: int| 0 <= i < yy@.len() && min_y == yy@[i];
                assert(combined_y[witness_i] == yy@.map(|_i: int, v: i8| v as int)[witness_i]);
                assert(combined_y[witness_i] == yy@[witness_i] as int);
                assert(combined_y[witness_i] == min_y as int);
                assert(combined_y.contains(min_y as int));
            }
            
            assert(forall|v: int| combined_x.contains(v) ==> v <= max_x as int);
            assert(forall|v: int| combined_y.contains(v) ==> v >= min_y as int);
            assert(max_x < min_y);
            assert(agreement_possible(n as int, m as int, x as int, y as int, xx@.map(|_i: int, v: i8| v as int), yy@.map(|_i: int, v: i8| v as int)));
        }
        return String::from_str("No War");
    } else {
        proof {
            assert(max_x as int >= min_y as int);
            assert(!agreement_possible(n as int, m as int, x as int, y as int, xx@.map(|_i: int, v: i8| v as int), yy@.map(|_i: int, v: i8| v as int)));
        }
        return String::from_str("War");
    }
}
// </vc-code>


}

fn main() {}