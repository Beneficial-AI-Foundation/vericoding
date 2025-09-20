// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(n: int, a: Seq<int>, p: Seq<char>) -> bool {
    n >= 2 &&
    a.len() == n &&
    p.len() == n - 1 &&
    (forall|i: int| 0 <= i < p.len() ==> #[trigger] p[i] == '0' || #[trigger] p[i] == '1') &&
    (forall|i: int| 0 <= i < a.len() ==> 1 <= #[trigger] a[i] <= n) &&
    a.to_set() =~= Set::new(|i: int| 1 <= i <= n)
}

spec fn max_up_to(a: Seq<int>, i: int) -> int
    recommends 0 <= i < a.len()
    decreases i when i >= 0
{
    if i == 0 { 
        a[0] 
    } else if i > 0 && a[i] > max_up_to(a, i-1) { 
        a[i] 
    } else if i > 0 { 
        max_up_to(a, i-1) 
    } else {
        a[0]
    }
}

spec fn can_sort(n: int, a: Seq<int>, p: Seq<char>) -> bool
    recommends valid_input(n, a, p)
{
    forall|i: int| 0 <= i < n - 1 ==> 
        (#[trigger] p[i] == '0' ==> max_up_to(a, i) <= i + 1)
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve(n: i8, a: Vec<i8>, p: Vec<char>) -> (result: String)
    requires
        valid_input(n as int, a@.map(|i, x| x as int), p@),
    ensures
        result@ == seq!['Y', 'E', 'S'] || result@ == seq!['N', 'O'],
        (result@ == seq!['Y', 'E', 'S']) <==> can_sort(n as int, a@.map(|i, x| x as int), p@),
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>


}

fn main() {}