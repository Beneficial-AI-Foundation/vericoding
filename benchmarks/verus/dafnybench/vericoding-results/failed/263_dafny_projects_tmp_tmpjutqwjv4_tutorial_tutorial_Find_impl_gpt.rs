use vstd::prelude::*;

verus! {

// Working through https://dafny.org/dafny/OnlineTutorial/guide

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



// https://dafny.org/dafny/OnlineTutorial/ValueTypes

spec fn update(s: Seq<int>, i: int, v: int) -> Seq<int> {
    s.subrange(0, i).add(seq![v]).add(s.subrange(i + 1, s.len() as int))
}


// https://dafny.org/dafny/OnlineTutorial/Lemmas



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
        forall|k: usize| k < 10 ==> // simplified constraint
            graph.contains(k) && k != i
}

spec fn path(p: Seq<usize>, graph: Set<usize>) -> bool
    decreases p.len()
{
    closed(graph) && 0 < p.len() &&
    graph.contains(p[0]) &&
    (p.len() > 1 ==> 
     path(p.subrange(1, p.len() as int), graph)) // and the rest of the sequence is a valid path
}

spec fn pathSpecific(p: Seq<usize>, start: usize, end: usize, graph: Set<usize>) -> bool {
    closed(graph) &&
    0 < p.len() && // path is nonempty
    start == p[0] && end == p[p.len() - 1] && // it starts and ends correctly
    path(p, graph) // and it is a valid path
}

// <vc-helpers>
/* no helpers needed */
// </vc-helpers>

// <vc-spec>
fn Find(a: &[int], key: int) -> (index: i32)
    ensures 
        0 <= index ==> index < a.len() && a[index as int] == key,
        index < 0 ==> (forall|k: int| 0 <= k < a.len() ==> a[k] != key),
// </vc-spec>
// <vc-code>
{
    let mut i: i32 = 0;
    while (i as int) < a.len()
        invariant
            0 <= (i as int),
            (i as int) <= a.len(),
            forall|k: int| 0 <= k < (i as int) ==> a[k] != key,
        decreases a.len() - (i as int)
    {
        assert(0 <= (i as int) && (i as int) < a.len());
        if a[i as int] == key {
            return i;
        } else {
            assert(a[i as int] != key);
            i = i + 1;
        }
    }
    assert(!((i as int) < a.len()));
    assert((i as int) <= a.len());
    assert((i as int) == a.len());
    proof {
        assert(forall|k: int| 0 <= k < a.len() ==> a[k] != key) by {
            assert forall|k: int| 0 <= k < a.len() implies a[k] != key by {
                if 0 <= k && k < a.len() {
                    assert(k < (i as int)); // since (i as int) == a.len()
                    assert(a[k] != key);
                }
            }
        }
    }
    -1
}
// </vc-code>

fn main() {}

}