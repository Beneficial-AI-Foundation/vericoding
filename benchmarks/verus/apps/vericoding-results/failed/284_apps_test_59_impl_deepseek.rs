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

proof fn max_up_to_lemma(a: Seq<int>, i: int, j: int) -> (m: int)
    requires
        0 <= i <= j < a.len(),
    ensures
        m == max_up_to(a, j),
        forall|k: int| i <= k <= j ==> a[k] <= m,
    decreases j - i
{
    if i == j {
        a[j]
    } else {
        let m = max_up_to_lemma(a, i + 1, j);
        if a[i] > m {
            a[i]
        } else {
            m
        }
    }
}

/* helper modified by LLM (iteration 5): add decreases clause to recursive lemma */
fn yes_string() -> String {
    "YES".to_string()
}

fn no_string() -> String {
    "NO".to_string()
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
    /* code modified by LLM (iteration 5): fix verification by using proper bounds */
    let mut max_so_far = a[0] as i32;
    let mut can_sort = true;
    
    for i in 0..(n as usize - 1) {
        proof {
            max_up_to_lemma(a@.map(|i, x| x as int), 0, i as int);
        }
        if p[i] == '0' {
            if max_so_far > (i + 1) as i32 {
                can_sort = false;
                break;
            }
        }
        if (a[i + 1] as i32) > max_so_far {
            max_so_far = a[i + 1] as i32;
        }
    }
    
    if can_sort {
        yes_string()
    } else {
        no_string()
    }
}
// </vc-code>


}

fn main() {}