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
proof fn lemma_skip_positions(a: &[int], i: int, k: int)
    requires
        forall|j: int| #![trigger a[j]] 0 <= j < a.len() ==> 0 <= a[j],
        forall|j: int| #![trigger a[j]] 0 < j < a.len() ==> a[j-1] - 1 <= a[j],
        0 <= i < a.len(),
        a[i] == k,
        k > 0,
    ensures
        forall|j: int| #![trigger a[j]] i < j < i + k && j < a.len() ==> a[j] > 0,
{
    let mut j = i + 1;
    while j < i + k && j < a.len()
        invariant
            i < j <= i + k,
            j <= a.len(),
            forall|m: int| #![trigger a[m]] i < m < j && m < a.len() ==> a[m] > 0,
    {
        assert(0 < j && j < a.len());
        assert(a[j-1] - 1 <= a[j]);
        
        if j - 1 == i {
            assert(a[i] == k);
            assert(a[j] >= k - 1);
            assert(k > 0);
            assert(a[j] > 0);
        } else {
            assert(i < j - 1 < j);
            assert(j - 1 < a.len());
            assert(a[j - 1] > 0);
            assert(a[j] >= a[j-1] - 1 >= 0);
            assert(a[j] > 0);
        }
        
        j = j + 1;
    }
}
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
    let mut i: usize = 0;
    while i < a.len()
        invariant
            i <= a.len(),
            forall|j: int| #![trigger a[j]] 0 <= j < i ==> a[j] != 0,
    {
        if a[i] == 0int {
            return i as i32;
        }
        
        assert(a[i] > 0int);
        if a[i] > 0int && i as int + a[i] < a.len() as int {
            let skip = a[i];
            proof {
                lemma_skip_positions(a, i as int, skip);
                assert(forall|j: int| #![trigger a[j]] (i as int < j < i as int + skip && j < a.len()) ==> a[j] > 0);
            }
            i = (i as int + skip) as usize;
        } else {
            i = i + 1;
        }
    }
    
    -1
}
// </vc-code>

fn main() {
}

}