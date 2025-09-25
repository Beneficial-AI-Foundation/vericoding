// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn is_valid_work_selection(n: int, k: int, c: int, s: Seq<char>, selection: Set<int>) -> bool
    recommends s.len() == n
{
    selection.len() == k &&
    (forall|day: int| #[trigger] selection.contains(day) ==> 0 <= day < n && day < s.len() && s[day] == 'o') &&
    (forall|day1: int, day2: int| selection.contains(day1) && selection.contains(day2) && day1 != day2 ==> 
        day1 < day2 - c || day2 < day1 - c)
}

spec fn count_available_days(s: Seq<char>) -> int {
    (Set::new(|i: int| 0 <= i < s.len() && s[i] == 'o')).len() as int
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve(n: i8, k: i8, c: i8, s: Vec<char>) -> (result: Vec<i8>)
    requires 
        n > 0,
        k > 0,
        c >= 0,
        k <= n,
        s.len() == n as usize,
        forall|i: int| 0 <= i < s@.len() ==> s@[i] == 'o' || s@[i] == 'x',
        count_available_days(s@) >= k as int,
        exists|valid_selection: Set<int>| is_valid_work_selection(n as int, k as int, c as int, s@, valid_selection),
    ensures
        forall|i: int| 0 <= i < result@.len() ==> 1 <= #[trigger] result@[i] as int <= n as int,
        forall|i: int| 0 <= i < result@.len() ==> s@[#[trigger] result@[i] as int - 1] == 'o',
        forall|i: int, j: int| 0 <= i < j < result@.len() ==> #[trigger] result@[i] as int < #[trigger] result@[j] as int,
        result@.len() <= k as usize,
// </vc-spec>
// <vc-code>
{
    assume(false);
    Vec::new()
}
// </vc-code>


}

fn main() {}