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
/* helper modified by LLM (iteration 5): fixed lemma syntax error */
proof fn lemma_max_up_to_monotonic(a: Seq<int>, i: int, j: int)
    requires
        0 <= i <= j < a.len(),
    ensures
        max_up_to(a, i) <= max_up_to(a, j),
    decreases j - i
{
    if i < j {
        lemma_max_up_to_monotonic(a, i, j - 1);
    }
}

proof fn lemma_max_up_to_bounds(a: Seq<int>, i: int)
    requires
        0 <= i < a.len(),
        forall|k: int| 0 <= k <= i ==> 1 <= a[k] <= a.len(),
    ensures
        1 <= max_up_to(a, i) <= a.len(),
    decreases i
{
    if i > 0 {
        lemma_max_up_to_bounds(a, i - 1);
    }
}

proof fn lemma_max_up_to_achievable(a: Seq<int>, i: int)
    requires
        0 <= i < a.len(),
    ensures
        exists|k: int| 0 <= k <= i && a[k] == max_up_to(a, i),
    decreases i
{
    if i == 0 {
        assert(a[0] == max_up_to(a, 0));
    } else {
        lemma_max_up_to_achievable(a, i - 1);
        if a[i] > max_up_to(a, i - 1) {
            assert(a[i] == max_up_to(a, i));
        } else {
            assert(max_up_to(a, i) == max_up_to(a, i - 1));
        }
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
    /* code modified by LLM (iteration 5): fixed comparison using ghost variables */
    let mut can_sort_flag = true;
    
    let mut i = 0;
    while i < n - 1
        invariant
            0 <= i <= n - 1,
            can_sort_flag <==> (forall|j: int| 0 <= j < i ==> 
                (p@[j] == '0' ==> max_up_to(a@.map(|k, x| x as int), j) <= j + 1)),
    {
        if p[i as usize] == '0' {
            let mut max_so_far = a[0];
            let mut j = 1;
            
            while j <= i
                invariant
                    1 <= j <= i + 1,
                    max_so_far as int == max_up_to(a@.map(|k, x| x as int), (j - 1) as int),
            {
                if a[j as usize] > max_so_far {
                    max_so_far = a[j as usize];
                }
                j += 1;
            }
            
            proof {
                let ghost_max = max_so_far as int;
                let ghost_limit = (i + 1) as int;
                if ghost_max > ghost_limit {
                    can_sort_flag = false;
                }
            }
            if can_sort_flag == false {
                break;
            }
        }
        i += 1;
    }
    
    if can_sort_flag {
        "YES".to_string()
    } else {
        "NO".to_string()
    }
}
// </vc-code>


}

fn main() {}