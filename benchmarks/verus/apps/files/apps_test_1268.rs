// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(a: Seq<int>, b: Seq<int>) -> bool {
    a.len() == b.len() && a.len() >= 2 && forall|i: int| 0 <= i < a.len() ==> 0 <= a[i] <= b[i]
}

spec fn sum_seq(s: Seq<int>) -> int
    decreases s.len()
{
    if s.len() == 0 { 0 }
    else { s[0] + sum_seq(s.subrange(1, s.len() as int)) }
}

spec fn find_two_largest_sum(s: Seq<int>) -> int
    requires s.len() >= 2
{
    let max1 = find_max(s);
    let max2 = find_max_excluding(s, max1);
    s[max1] + s[max2]
}

spec fn find_max(s: Seq<int>) -> int
    requires s.len() >= 1
    ensures 0 <= find_max(s) < s.len()
    decreases s.len()
{
    if s.len() == 1 { 0 }
    else {
        let rest_max = find_max(s.subrange(1, s.len() as int));
        if s[0] >= s[rest_max + 1] { 0 } else { rest_max + 1 }
    }
}

spec fn find_max_excluding(s: Seq<int>, exclude: int) -> int
    requires s.len() >= 2
    requires 0 <= exclude && exclude < s.len()
    ensures 0 <= find_max_excluding(s, exclude) < s.len()
    ensures find_max_excluding(s, exclude) != exclude
    decreases s.len()
{
    if exclude == 0 {
        1 + find_max(s.subrange(1, s.len() as int))
    } else if exclude == s.len() - 1 {
        find_max(s.subrange(0, s.len() - 1))
    } else {
        let left_max = if s.subrange(0, exclude).len() > 0 { find_max(s.subrange(0, exclude)) } else { -1 };
        let right_max = if s.subrange(exclude + 1, s.len() as int).len() > 0 { 
            exclude + 1 + find_max(s.subrange(exclude + 1, s.len() as int)) 
        } else { -1 };
        if left_max == -1 { right_max }
        else if right_max == -1 { left_max }
        else if s[left_max] >= s[right_max] { left_max } else { right_max }
    }
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve(a: Seq<int>, b: Seq<int>) -> (result: String)
    requires valid_input(a, b)
    ensures result == "YES" || result == "NO"
    ensures result == "YES" <==> find_two_largest_sum(b) >= sum_seq(a)
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>


}

fn main() {}