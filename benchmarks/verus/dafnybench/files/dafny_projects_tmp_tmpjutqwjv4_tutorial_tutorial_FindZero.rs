// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn fib(n: nat) -> nat 
    decreases n
{
    if n == 0 { 0nat }
    else if n == 1 { 1nat }
    else { fib((n - 1) as nat) + fib((n - 2) as nat) }
}

spec fn sorted(a: Seq<int>) -> bool {
    forall|n: int, m: int| 0 <= n < m < a.len() ==> a[n] <= a[m]
}

spec fn update(s: Seq<int>, i: int, v: int) -> Seq<int>
{
    s.subrange(0, i).add(seq![v]).add(s.subrange(i + 1, s.len() as int))
}

spec fn count(a: Seq<bool>) -> nat
    decreases a.len()
{
    if a.len() == 0 { 
        0nat
    } else {
        (if a[0] { 1nat } else { 0nat }) + count(a.subrange(1, a.len() as int))
    }
}

struct Node {
    next: Seq<int>,
}

spec fn closed(graph: Set<int>) -> bool {
    true
}

spec fn path(p: Seq<int>, graph: Set<int>) -> bool 
    decreases p.len()
{
    closed(graph) && 0 < p.len() &&
    graph.contains(p[0]) &&
    (p.len() > 1 ==> 
        path(p.subrange(1, p.len() as int), graph))
}

spec fn path_specific(p: Seq<int>, start: int, end: int, graph: Set<int>) -> bool {
    closed(graph) &&
    0 < p.len() &&
    start == p[0] && end == p[p.len() - 1] &&
    path(p, graph)
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn find_zero(a: &[int]) -> (index: i32)
    requires 
        forall|i: int| #![trigger a[i]] 0 <= i < a.len() ==> 0 <= a[i],
        forall|i: int| #![trigger a[i]] 0 < i < a.len() ==> a[i-1] - 1 <= a[i],
    ensures 
        index < 0 ==> forall|i: int| #![trigger a[i]] 0 <= i < a.len() ==> a[i] != 0,
        0 <= index ==> index < a.len() && a[index as int] == 0,
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}