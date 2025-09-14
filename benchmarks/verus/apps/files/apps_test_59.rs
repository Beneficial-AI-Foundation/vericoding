// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(n: int, a: Seq<int>, p: Seq<char>) -> bool {
    n >= 2 &&
    a.len() == n &&
    p.len() == n - 1 &&
    (forall|i: int| 0 <= i < p.len() ==> p[i] == '0' || p[i] == '1') &&
    (forall|i: int| 0 <= i < a.len() ==> 1 <= a[i] <= n) &&
    (forall|i: int| 1 <= i <= n ==> exists|j: int| 0 <= j < a.len() && a[j] == i)
}

spec fn max_up_to(a: Seq<int>, i: int) -> int
    recommends 0 <= i < a.len()
    decreases i
{
    if i == 0 { 
        a[0] 
    } else if a[i] > max_up_to(a, i-1) { 
        a[i] 
    } else { 
        max_up_to(a, i-1) 
    }
}

spec fn can_sort(n: int, a: Seq<int>, p: Seq<char>) -> bool
    recommends valid_input(n, a, p)
{
    forall|i: int| 0 <= i < n - 1 ==> 
        (p[i] == '0' ==> max_up_to(a, i) <= i + 1)
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve(n: int, a: Seq<int>, p: Seq<char>) -> (result: Seq<char>)
    requires 
        valid_input(n, a, p),
    ensures 
        result == seq!['Y', 'E', 'S'] || result == seq!['N', 'O'],
        (result == seq!['Y', 'E', 'S']) <==> can_sort(n, a, p),
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>


}

fn main() {}