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
proof fn lemma_monotonic_search(a: Seq<int>, i: int, j: int)
    requires
        0 <= i <= j < a.len(),
        forall|k: int| 0 <= k < a.len() ==> 0 <= a[k],
        forall|k: int| 0 < k < a.len() ==> a[k-1] - 1 <= a[k],
    ensures
        forall|k: int| i <= k <= j ==> a[i] - (k - i) <= a[k]
    decreases j - i
{
    if i < j {
        lemma_monotonic_search(a, i, j - 1);
        assert(a[j-1] - 1 <= a[j]);
        assert(a[i] - ((j-1) - i) <= a[j-1]);
        assert(a[i] - (j - i) <= a[j]);
    }
}

proof fn lemma_zero_exists(a: Seq<int>, i: int)
    requires
        0 <= i < a.len(),
        forall|k: int| 0 <= k < a.len() ==> 0 <= a[k],
        forall|k: int| 0 < k < a.len() ==> a[k-1] - 1 <= a[k],
        a[i] <= i,
    ensures
        exists|k: int| 0 <= k <= i && a[k] == 0
    decreases i
{
    if a[i] == 0 {
    } else if i > 0 {
        assert(a[i-1] - 1 <= a[i]);
        assert(a[i-1] <= a[i] + 1);
        assert(a[i-1] <= i - 1);
        lemma_zero_exists(a, i - 1);
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
    let mut low: usize = 0;
    let mut high: usize = a.len();
    let mut index: i32 = -1;
    
    while low < high
        invariant
            0 <= low <= high <= a.len(),
            forall|i: int| 0 <= i < low ==> a[i] > 0,
            exists|i: int| low <= i < high && a[i] <= (i - low as int) ==> index >= 0 || exists|j: int| low <= j < high && a[j] == 0,
        decreases high - low
    {
        let mid = low + (high - low) / 2;
        
        if a[mid] == 0 {
            index = mid as i32;
            break;
        }
        
        proof {
            lemma_monotonic_search(a.seq(), low as int, mid as int);
        }
        
        if a[mid] > (mid - low) as int {
            assert(forall|i: int| low as int <= i <= mid as int ==> a.seq()[i] >= a.seq()[low as int] - (i - low as int));
            assert(forall|i: int| low <= i <= mid ==> a[i] > 0);
            low = mid + 1;
        } else {
            proof {
                lemma_zero_exists(a.seq(), mid as int);
            }
            high = mid;
        }
    }
    
    if index >= 0 {
        assert(0 <= index < a.len() as i32 && a[index as usize] == 0);
    } else {
        assert(forall|i: int| 0 <= i < a.len() ==> a[i] != 0);
    }
    
    index
}
// </vc-code>

fn main() {
}

}