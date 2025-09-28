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
/* helper modified by LLM (iteration 5): updated comment */
proof fn lemma_max_up_to_unfold(a: Seq<int>, i: int)
    requires
        1 <= i < a.len(),
    ensures
        max_up_to(a, i) == if a[i] > max_up_to(a, i - 1) { a[i] } else { max_up_to(a, i - 1) },
{
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
    /* code modified by LLM (iteration 5): fixed compilation error by removing ghost casts from executable code */
    let ghost a_int = a@.map(|_idx, x| x as int);
    let mut i: i8 = 0;
    let mut current_max = a[0];

    while i < n - 1
        invariant
            a@.len() == n as int,
            p@.len() == n as int - 1,
            a_int === a@.map(|_idx, x| x as int),
            valid_input(n as int, a_int, p@),
            0 <= i < n,
            forall|k: int| 0 <= k < i as int ==> #[trigger] (p@[k] == '0' ==> max_up_to(a_int, k) <= k + 1),
            current_max as int == max_up_to(a_int, i as int),
        decreases n - 1 - i
    {
        if p[i as usize] == '0' {
            if current_max > i + 1 {
                proof {
                    let j = i as int;
                    assert(p@[j] == '0');
                    assert(max_up_to(a_int, j) > j + 1);
                    assert(!can_sort(n as int, a_int, p@));
                }
                return "NO".to_string();
            }
        }

        i = i + 1;
        
        proof {
            lemma_max_up_to_unfold(a_int, i as int);
        }

        if a[i as usize] > current_max {
            current_max = a[i as usize];
        }
    }

    proof {
        assert(i == n - 1);
        assert(forall|k: int| 0 <= k < (n - 1) as int ==> (p@[k] == '0' ==> max_up_to(a_int, k) <= k + 1));
        assert(can_sort(n as int, a_int, p@));
    }
    "YES".to_string()
}
// </vc-code>


}

fn main() {}