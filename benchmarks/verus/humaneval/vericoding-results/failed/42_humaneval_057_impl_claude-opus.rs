// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn monotonic(l: Seq<int>) -> bool {
    if l.len() <= 1 {
        true
    } else {
        let increasing = forall|i: nat| #![trigger l[i as int]] i < l.len() - 1 ==> l[i as int] <= l[(i + 1) as int];
        let decreasing = forall|i: nat| #![trigger l[i as int]] i < l.len() - 1 ==> l[i as int] >= l[(i + 1) as int];
        increasing || decreasing
    }
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn is_monotonic(l: Vec<i8>) -> (result: bool)
    ensures result == monotonic(l@.map(|_i: int, x: i8| x as int))
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed invariants to properly prove postcondition */
    if l.len() <= 1 {
        return true;
    }
    
    let mut increasing = true;
    let mut decreasing = true;
    let mut i: usize = 0;
    
    while i < l.len() - 1
        invariant
            0 <= i <= l.len() - 1,
            increasing == (forall|j: nat| #![trigger l@[j as int]] j < i ==> l@[j as int] as int <= l@[(j + 1) as int] as int),
            decreasing == (forall|j: nat| #![trigger l@[j as int]] j < i ==> l@[j as int] as int >= l@[(j + 1) as int] as int),
        decreases l.len() - 1 - i
    {
        if l[i] > l[i + 1] {
            increasing = false;
        }
        if l[i] < l[i + 1] {
            decreasing = false;
        }
        i = i + 1;
    }
    
    proof {
        assert(i == l.len() - 1);
        assert(increasing == (forall|j: nat| #![trigger l@[j as int]] j < l.len() - 1 ==> l@[j as int] as int <= l@[(j + 1) as int] as int));
        assert(decreasing == (forall|j: nat| #![trigger l@[j as int]] j < l.len() - 1 ==> l@[j as int] as int >= l@[(j + 1) as int] as int));
        let mapped = l@.map(|_i: int, x: i8| x as int);
        assert(forall|j: nat| #![trigger mapped[j as int]] j < mapped.len() - 1 ==> mapped[j as int] == l@[j as int] as int);
        assert(increasing || decreasing == monotonic(mapped));
    }
    
    increasing || decreasing
}
// </vc-code>


}

fn main() {}