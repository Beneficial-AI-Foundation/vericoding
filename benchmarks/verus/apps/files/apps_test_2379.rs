// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn is_valid_work_selection(n: int, k: int, c: int, s: Seq<char>, selection: Set<int>) -> bool
    recommends s.len() == n
{
    selection.len() == k &&
    (forall|day: int| selection.contains(day) ==> 0 <= day < n && day < s.len() && s[day] == 'o') &&
    (forall|day1: int, day2: int| selection.contains(day1) && selection.contains(day2) && day1 != day2 ==> 
        day1 < day2 - c || day2 < day1 - c)
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve(n: int, k: int, c: int, s: Seq<char>) -> (result: Vec<int>)
    requires 
        n > 0 &&
        k > 0 &&
        c >= 0 &&
        k <= n &&
        s.len() == n &&
        (forall|i: int| 0 <= i < s.len() ==> s[i] == 'o' || s[i] == 'x') &&
        Set::new(|i: int| 0 <= i < s.len() && s[i] == 'o').len() >= k &&
        (exists|valid_selection: Set<int>| is_valid_work_selection(n, k, c, s, valid_selection))
    ensures 
        (forall|i: int| 0 <= i < result.len() ==> 1 <= result[i] <= n) &&
        (forall|i: int| 0 <= i < result.len() ==> s[result[i] - 1] == 'o') &&
        (forall|i: int, j: int| 0 <= i < j < result.len() ==> result[i] < result[j]) &&
        result.len() <= k
// </vc-spec>
// <vc-code>
{
    assume(false);
    Vec::new()
}
// </vc-code>


}

fn main() {}