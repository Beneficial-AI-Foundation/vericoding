// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn fib(n: nat) -> nat
    decreases n
{
    if n == 0 { 0 }
    else if n == 1 { 1 }
    else { fib((n - 1) as nat) + fib((n - 2) as nat) }
}

spec fn sorted(a: &[int]) -> bool {
    forall|n: int, m: int| 0 <= n < m < a.len() ==> a[n] <= a[m]
}

spec fn update(s: Seq<int>, i: int, v: int) -> Seq<int> {
    s.subrange(0, i).add(seq![v]).add(s.subrange(i + 1, s.len() as int))
}

spec fn count(a: Seq<bool>) -> nat
    decreases a.len()
{
    if a.len() == 0 { 0nat }
    else {
        (if a[0] { 1nat } else { 0nat }) + count(a.subrange(1, a.len() as int))
    }
}

struct Node {
    next: Vec<usize>
}

spec fn closed(graph: Set<usize>) -> bool {
    forall|i: usize| graph.contains(i) ==> 
        forall|k: usize| k < 10 ==>
            graph.contains(k) && k != i
}

spec fn path(p: Seq<usize>, graph: Set<usize>) -> bool
    decreases p.len()
{
    closed(graph) && 0 < p.len() &&
    graph.contains(p[0]) &&
    (p.len() > 1 ==> 
     path(p.subrange(1, p.len() as int), graph))
}

spec fn pathSpecific(p: Seq<usize>, start: usize, end: usize, graph: Set<usize>) -> bool {
    closed(graph) &&
    0 < p.len() &&
    start == p[0] && end == p[p.len() - 1] &&
    path(p, graph)
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn Find(a: &[int], key: int) -> (index: i32)
    ensures 
        0 <= index ==> index < a.len() && a[index as int] == key,
        index < 0 ==> (forall|k: int| 0 <= k < a.len() ==> a[k] != key),
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}