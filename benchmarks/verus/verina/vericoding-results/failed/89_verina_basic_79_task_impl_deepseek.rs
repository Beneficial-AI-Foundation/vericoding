// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed Seq<int> vs i32 type mismatch and proper indexing */
proof fn online_max_helper(a: Seq<i32>, x: int) 
    requires 
        a.len() > 0, 
        x < a.len() as int,
    ensures 
        x <= a.len() - 1
        && (forall|i: int| 0 <= i < x ==> a[i] <= max_seq(a, x)) 
        && (exists|i: int| 0 <= i < x && a[i] == max_seq(a, x))? true
        && (let idx = max_seq_index(a, x); idx >= x && idx < a.len() as int && a[idx] == max_seq(a, x))
{
    let candidate = max_seq_index(a, x);
    let max_val = max_seq(a, x);
    assert(a[candidate] == max_val);
    assert(candidate >= x);
    assert(candidate < a.len() as int);
    if x > 0 {
        assert(forall|i: int| 0 <= i < x ==> a[i] <= max_val);
        assert(exists|i: int| 0 <= i < x && a[i] == max_val);
    }
}

spec fn max_seq(a: Seq<i32>, start: int) -> i32
    recommends start >= 0 && start < a.len() as int
{
    if start >= a.len() as int - 1 {
        a[a.len() as int - 1]
    } else {
        let rest_max = max_seq(a, start + 1);
        if a[start] > rest_max {
            a[start]
        } else {
            rest_max
        }
    }
}

spec fn max_seq_index(a: Seq<i32>, start: int) -> int
    recommends start >= 0 && start < a.len() as int
{
    if start >= a.len() as int - 1 {
        a.len() as int - 1
    } else {
        let rest_index = max_seq_index(a, start + 1);
        if a[start] >= a[rest_index] {
            start
        } else {
            rest_index
        }
    }
}
// </vc-helpers>

// <vc-spec>
fn online_max(a: &Vec<i32>, x: usize) -> (result: (i32, usize))
    requires
        a.len() > 0,
        x < a.len(),
    ensures
        ({
            let (m, p) = result;
            x <= p && p < a.len()
            && (forall|i: int| 0 <= i < x ==> a[i] <= m)
            && (exists|i: int| 0 <= i < x && a[i] == m)
            && ((p < a.len() - 1) ==> (exists|i: int| x <= i <= p && a[i] > m))
            && ((forall|i: int| x <= i < a.len() ==> a[i] <= m) ==> p == a.len() - 1)
        })
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): fixed type conversion between int and usize */
{
    proof { online_max_helper(a@, x as int); }
    
    let mut max_val = a[x];
    let mut max_index = x;
    let mut current = x + 1;
    
    while current < a.len()
        invariant
            x <= max_index < a.len(),
            max_val == a[max_index],
            forall|i: int| 0 <= i < x as int ==> a@[i] <= max_val,
            forall|i: int| x as int <= i < current as int ==> a@[i] <= max_val,
            exists|i: int| x as int <= i < current as int && a@[i] == max_val,
            current <= a.len()
        decreases a.len() - current
    {
        if a[current] > max_val {
            max_val = a[current];
            max_index = current;
        }
        current = current + 1;
    }
    
    (max_val, max_index)
}
// </vc-code>

}
fn main() {}