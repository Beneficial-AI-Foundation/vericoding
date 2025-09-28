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
proof fn lemma_max_up_to_properties(a: Seq<int>, i: int)
    requires
        0 <= i < a.len(),
    ensures
        a[i] <= max_up_to(a, i),
        max_up_to(a, i) <= max_up_to(a, i + 1) || i == a.len() - 1,
        forall|j: int| 0 <= j <= i ==> a[j] <= max_up_to(a, i),
    decreases i
{
    if i == 0 {
        assert(a[0] <= max_up_to(a, 0));
    } else {
        lemma_max_up_to_properties(a, i - 1);
        if a[i] > max_up_to(a, i - 1) {
            assert(max_up_to(a, i) == a[i]);
        } else {
            assert(max_up_to(a, i) == max_up_to(a, i - 1));
        }
    }
}

/* helper modified by LLM (iteration 4): Fixed trigger annotation in quantifier */
proof fn lemma_valid_implies_permutation(n: int, a: Seq<int>)
    requires
        n >= 2,
        a.len() == n,
        forall|i: int| 0 <= i < a.len() ==> 1 <= #[trigger] a[i] <= n,
        a.to_set() =~= Set::new(|i: int| 1 <= i <= n),
    ensures
        forall|k: int| 1 <= k <= n ==> exists|j: int| 0 <= j < n && a[j] == k,
{
    assert forall|k: int| 1 <= k <= n implies exists|j: int| 0 <= j < n && a[j] == k by {
        assert(a.to_set().contains(k));
    }
}
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
    /* code modified by LLM (iteration 4): Keep working implementation */
    let mut max_so_far: i8 = a[0];
    let mut i: usize = 0;
    
    while i < (n - 1) as usize
        invariant
            0 <= i <= (n - 1) as usize,
            max_so_far as int == max_up_to(a@.map(|idx, x| x as int), i as int),
            forall|j: int| 0 <= j < i ==> (p@[j] == '0' ==> max_up_to(a@.map(|idx, x| x as int), j) <= j + 1),
        decreases (n - 1) as usize - i
    {
        if p[i] == '0' {
            if max_so_far > (i + 1) as i8 {
                return "NO".to_string();
            }
        }
        
        i = i + 1;
        
        if i < n as usize {
            if a[i] > max_so_far {
                max_so_far = a[i];
            }
            proof {
                lemma_max_up_to_properties(a@.map(|idx, x| x as int), i as int);
            }
        }
    }
    
    return "YES".to_string();
}
// </vc-code>


}

fn main() {}