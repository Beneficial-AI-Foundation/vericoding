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
proof fn lemma_first_zero_bounds(a: &[int], i: int)
    requires
        forall|j: int| #![trigger a[j]] 0 <= j < a.len() ==> 0 <= a[j],
        forall|j: int| #![trigger a[j]] 0 < j < a.len() ==> a[j-1] - 1 <= a[j],
        0 <= i < a.len(),
        a[i as int] == 0,
    ensures
        a[0] <= 1,
        forall|k: int| 0 <= k <= i ==> a[k] <= (1 + k),
{
    assert(a[i as int] == 0);
    
    if i == 0 {
        assert(a[0] == 0);
        assert(a[0] <= 1);
    } else {
        let mut j: int = 1;
        while j <= i
            invariant
                1 <= j <= i + 1,
                forall|k: int| 0 <= k < j ==> a[k] <= (1 + k),
        {
            if j == 1 {
                assert(a[0] >= 0);
                assert(a[0] - 1 <= a[1]);
                assert(a[0] <= 1);
            } else {
                assert(a[j-1] - 1 <= a[j]);
                assert(a[j-1] <= 1 + (j-1));
                assert(a[j] >= a[j-1] - 1);
                assert(a[j] >= (1 + j - 1) - 1);
                assert(a[j] >= j - 1);
                if j < i {
                    assert(a[j] >= 0);
                } else if j == i {
                    assert(a[j] == 0);
                    assert(j - 1 <= 0);
                }
            }
            j = j + 1;
        }
    }
}

proof fn lemma_no_zero_exists(a: &[int], i: int)
    requires
        forall|j: int| #![trigger a[j]] 0 <= j < a.len() ==> 0 <= a[j],
        forall|j: int| #![trigger a[j]] 0 < j < a.len() ==> a[j-1] - 1 <= a[j],
        0 <= i < a.len(),
        a[0] >= 1,
    ensures
        a[i] >= 1,
{
    if i == 0 {
        assert(a[0] >= 1);
    } else {
        let mut j: int = 1;
        while j <= i
            invariant
                1 <= j <= i + 1,
                forall|k: int| 0 <= k < j ==> a[k] >= 1,
        {
            assert(a[j-1] - 1 <= a[j]);
            assert(a[j-1] >= 1);
            assert(a[j] >= a[j-1] - 1);
            assert(a[j] >= 1 - 1);
            assert(a[j] >= 0);
            assert(a[j] >= 1);
            j = j + 1;
        }
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
    if a.len() == 0 {
        return -1;
    }
    
    if a[0] == 0int {
        return 0;
    }
    
    if a[0] >= 2int {
        proof {
            lemma_no_zero_exists(a, 0);
            if a.len() > 1 {
                lemma_no_zero_exists(a, 1);
            }
        }
        return -1;
    }
    
    assert(a[0] == 1int);
    
    let mut i = 1;
    while i < a.len()
        invariant
            1 <= i <= a.len(),
            a[0] == 1int,
            forall|j: int| 0 <= j < i ==> a[j] != 0int,
            forall|j: int| #![trigger a[j]] 0 <= j < a.len() ==> 0 <= a[j],
            forall|j: int| #![trigger a[j]] 0 < j < a.len() ==> a[j-1] - 1 <= a[j],
    {
        if a[i] == 0int {
            return i as i32;
        }
        i += 1;
    }
    
    -1
}
// </vc-code>

fn main() {
}

}