use vstd::prelude::*;

verus! {

// Working through https://dafny.org/dafny/OnlineTutorial/guide

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



// https://dafny.org/dafny/OnlineTutorial/ValueTypes

spec fn update(s: Seq<int>, i: int, v: int) -> Seq<int>
{
    s.subrange(0, i).add(seq![v]).add(s.subrange(i + 1, s.len() as int))
}


// https://dafny.org/dafny/OnlineTutorial/Lemmas

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
    next: Seq<int>, // Using int IDs instead of references for simplicity
}

spec fn closed(graph: Set<int>) -> bool {
    true // Simplified for translation
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
    0 < p.len() && // path is nonempty
    start == p[0] && end == p[p.len() - 1] && // it starts and ends correctly
    path(p, graph) // and it is a valid path
}

// <vc-helpers>
proof fn lemma_monotonic_implies_early_zero(a: &[int], j: int)
    requires 
        forall|i: int| #![trigger a[i]] 0 <= i < a.len() ==> 0 <= a[i],
        forall|i: int| #![trigger a[i]] 0 < i < a.len() ==> a[i-1] - 1 <= a[i],
        0 <= j < a.len(),
        a[j] == 0,
    ensures
        forall|i: int| #![trigger a[i]] 0 <= i <= j ==> a[i] == 0,
{
    if j > 0 {
        assert(a[j-1] - 1 <= a[j]);
        assert(a[j-1] - 1 <= 0);
        assert(a[j-1] <= 1);
        assert(0 <= a[j-1]);
        assert(a[j-1] == 0 || a[j-1] == 1);
        if a[j-1] == 1 {
            assert(a[j-1] - 1 == 0);
            assert(0 <= a[j]);
            assert(a[j] == 0);
        } else {
            assert(a[j-1] == 0);
        }
        if a[j-1] == 0 {
            lemma_monotonic_implies_early_zero(a, j-1);
        }
    }
}

proof fn lemma_search_correctness(a: &[int], i: int)
    requires 
        forall|k: int| #![trigger a[k]] 0 <= k < a.len() ==> 0 <= a[k],
        forall|k: int| #![trigger a[k]] 0 < k < a.len() ==> a[k-1] - 1 <= a[k],
        0 <= i < a.len(),
        a[i] < i,
    ensures
        exists|j: int| 0 <= j <= i && a[j] == 0,
{
    if i == 0 {
        assert(a[0] < 0);
        assert(0 <= a[0]);
        assert(false);
    } else {
        if a[i] == 0 {
            assert(a[i] == 0);
        } else {
            assert(a[i-1] - 1 <= a[i]);
            assert(a[i-1] <= a[i] + 1);
            assert(a[i-1] <= i - 1 + 1);
            assert(a[i-1] <= i);
            if a[i-1] < i - 1 {
                lemma_search_correctness(a, i-1);
            } else {
                assert(a[i-1] <= i);
                assert(a[i-1] >= i);
                assert(a[i-1] == i);
                assert(a[i-1] - 1 == i - 1);
                assert(a[i-1] - 1 <= a[i]);
                assert(i - 1 <= a[i]);
                assert(a[i] >= i - 1);
                assert(a[i] < i);
                assert(a[i] == i - 1);
            }
        }
    }
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
fn find_zero(a: &[int]) -> (index: i32)
    requires 
        forall|i: int| #![trigger a[i]] 0 <= i < a.len() ==> 0 <= a[i],
        forall|i: int| #![trigger a[i]] 0 < i < a.len() ==> a[i-1] - 1 <= a[i],
    ensures 
        index < 0 ==> forall|i: int| #![trigger a[i]] 0 <= i < a.len() ==> a[i] != 0,
        0 <= index ==> index < a.len() && a[index as int] == 0,
// </vc-spec>
// </vc-spec>

// <vc-code>
{
    for i in 0..a.len()
        invariant
            forall|k: int| #![trigger a[k]] 0 <= k < a.len() ==> 0 <= a[k],
            forall|k: int| #![trigger a[k]] 0 < k < a.len() ==> a[k-1] - 1 <= a[k],
            forall|k: int| #![trigger a[k]] 0 <= k < i ==> a[k] != 0,
    {
        if a[i as int] == 0 {
            return i as i32;
        }
        
        let ghost i_int = i as int;
        if a[i_int] < i_int {
            proof {
                lemma_search_correctness(a, i_int);
            }
            assert(exists|j: int| 0 <= j <= i && a[j] == 0);
            assert(forall|k: int| #![trigger a[k]] 0 <= k < i ==> a[k] != 0);
            assert(false);
        }
    }
    -1
}
// </vc-code>

fn main() {
}

}