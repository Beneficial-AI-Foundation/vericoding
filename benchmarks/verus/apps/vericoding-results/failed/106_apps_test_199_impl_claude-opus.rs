// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(n: int, s: int, v: Seq<int>) -> bool {
    n > 0 && v.len() == n && s >= 0 && forall|i: int| 0 <= i < v.len() ==> v[i] >= 0
}

spec fn sum(v: Seq<int>) -> int
    decreases v.len()
{
    if v.len() == 0 {
        0
    } else {
        v[0] + sum(v.subrange(1, v.len() as int))
    }
}

spec fn min_seq(v: Seq<int>) -> int
    recommends v.len() > 0
    decreases v.len()
{
    if v.len() == 1 {
        v[0]
    } else if v.len() > 1 && v[0] <= min_seq(v.subrange(1, v.len() as int)) {
        v[0]
    } else if v.len() > 1 {
        min_seq(v.subrange(1, v.len() as int))
    } else {
        0
    }
}

spec fn min(a: int, b: int) -> int {
    if a <= b { a } else { b }
}
// </vc-preamble>

// <vc-helpers>
proof fn sum_non_negative(v: Seq<int>)
    requires
        forall|i: int| 0 <= i < v.len() ==> v[i] >= 0
    ensures
        sum(v) >= 0
    decreases v.len()
{
    if v.len() == 0 {
    } else {
        sum_non_negative(v.subrange(1, v.len() as int));
    }
}

proof fn min_seq_in_seq(v: Seq<int>)
    requires
        v.len() > 0
    ensures
        exists|i: int| 0 <= i < v.len() && v[i] == min_seq(v)
    decreases v.len()
{
    if v.len() == 1 {
    } else {
        min_seq_in_seq(v.subrange(1, v.len() as int));
    }
}

proof fn min_seq_lower_bound(v: Seq<int>)
    requires
        v.len() > 0
    ensures
        forall|i: int| 0 <= i < v.len() ==> min_seq(v) <= v[i]
    decreases v.len()
{
    if v.len() == 1 {
    } else {
        min_seq_lower_bound(v.subrange(1, v.len() as int));
    }
}

proof fn min_seq_non_negative(v: Seq<int>)
    requires
        v.len() > 0,
        forall|i: int| 0 <= i < v.len() ==> v[i] >= 0
    ensures
        min_seq(v) >= 0
{
    min_seq_in_seq(v);
}
// </vc-helpers>

// <vc-spec>
fn solve(n: i8, s: i8, v: Vec<i8>) -> (result: i8)
    requires 
        valid_input(n as int, s as int, v@.map(|i, x| x as int))
    ensures 
        sum(v@.map(|i, x| x as int)) < s as int ==> result == -1,
        sum(v@.map(|i, x| x as int)) >= s as int ==> result == min((sum(v@.map(|i, x| x as int)) - s as int) / n as int, min_seq(v@.map(|i, x| x as int))) as i8,
        result == -1 || result >= 0
// </vc-spec>
// <vc-code>
{
    let v_spec = v@.map(|i, x| x as int);
    let mut total: i32 = 0;
    let mut min_val: i8 = 127;
    let mut i: usize = 0;
    
    while i < v.len()
        invariant
            i <= v.len(),
            total == sum(v_spec.subrange(0, i as int)) as i32,
            i > 0 ==> min_val == min_seq(v_spec.subrange(0, i as int)) as i8,
            i == 0 ==> min_val == 127,
            forall|j: int| 0 <= j < i ==> v_spec[j] >= 0,
            v_spec == v@.map(|i, x| x as int)
    {
        total = total + v[i] as i32;
        if i == 0 || v[i] < min_val {
            min_val = v[i];
        }
        i = i + 1;
    }
    
    proof {
        sum_non_negative(v_spec);
        if v.len() > 0 {
            min_seq_non_negative(v_spec);
            min_seq_lower_bound(v_spec);
        }
    }
    
    if total < s as i32 {
        return -1;
    } else {
        let excess = (total - s as i32) / n as i32;
        if excess < min_val as i32 {
            return excess as i8;
        } else {
            return min_val;
        }
    }
}
// </vc-code>


}

fn main() {}