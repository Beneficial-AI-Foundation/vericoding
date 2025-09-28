// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(n: int, m: int, a: Seq<int>) -> bool {
    n >= 1 && m >= 1 && a.len() == n && 
    (forall|i: int| 0 <= i < a.len() ==> a[i] >= 1)
}

spec fn valid_output(result: Seq<int>, n: int) -> bool {
    result.len() == n && (forall|i: int| 0 <= i < result.len() ==> result[i] >= 0)
}

spec fn compute_page_turns(a: Seq<int>, m: int, i: int, s: int) -> int
    recommends m >= 1, i >= 0, s >= 0
{
    if i >= a.len() { 0 }
    else { (s + a[i]) / m }
}

spec fn compute_next_state(a: Seq<int>, m: int, i: int, s: int) -> int
    recommends m >= 1, i >= 0, s >= 0
{
    if i >= a.len() { s }
    else { (s + a[i]) % m }
}

spec fn correct_page_turns(result: Seq<int>, a: Seq<int>, m: int) -> bool
    recommends m >= 1
{
    result.len() == a.len() &&
    (forall|i: int| 0 <= i < a.len() ==> {
        let s = compute_state_at(a, m, i);
        #[trigger] result[i] == (s + a[i]) / m
    })
}

spec fn compute_state_at(a: Seq<int>, m: int, day: int) -> int
    recommends m >= 1, day >= 0
    decreases day
{
    if day <= 0 { 0 }
    else if day > a.len() { compute_state_at(a, m, a.len() as int) }
    else if day > 0 && day <= a.len() { (compute_state_at(a, m, day - 1) + a[day - 1]) % m }
    else { 0 }
}
// </vc-preamble>

// <vc-helpers>
proof fn lemma_state_computation(a: Seq<int>, m: int, i: nat)
    requires
        m >= 1,
        i <= a.len(),
        forall|j: int| 0 <= j < a.len() ==> a[j] >= 1
    ensures
        compute_state_at(a, m, i as int) >= 0,
        compute_state_at(a, m, i as int) < m
    decreases i
{
    if i == 0 {
        assert(compute_state_at(a, m, 0) == 0);
    } else {
        lemma_state_computation(a, m, (i - 1) as nat);
        assert(compute_state_at(a, m, i as int) == (compute_state_at(a, m, (i - 1) as int) + a[(i - 1) as int]) % m);
        assert((compute_state_at(a, m, (i - 1) as int) + a[(i - 1) as int]) % m >= 0);
        assert((compute_state_at(a, m, (i - 1) as int) + a[(i - 1) as int]) % m < m);
    }
}

proof fn lemma_state_matches_loop(a: Seq<int>, m: int, i: nat, s: int)
    requires
        m >= 1,
        i <= a.len(),
        s == compute_state_at(a, m, i as int),
        forall|j: int| 0 <= j < a.len() ==> a[j] >= 1
    ensures
        s >= 0,
        s < m,
        if i < a.len() {
            compute_state_at(a, m, (i + 1) as int) == (s + a[i as int]) % m
        } else {
            true
        }
{
    lemma_state_computation(a, m, i);
    if i < a.len() {
        assert(compute_state_at(a, m, (i + 1) as int) == (compute_state_at(a, m, i as int) + a[i as int]) % m);
        assert(compute_state_at(a, m, (i + 1) as int) == (s + a[i as int]) % m);
    }
}
// </vc-helpers>

// <vc-spec>
fn solve(n: i8, m: i8, a: Vec<i8>) -> (result: Vec<i8>)
requires
    valid_input(n as int, m as int, a@.map(|i: int, x: i8| x as int))
ensures
    valid_output(result@.map(|i: int, x: i8| x as int), n as int),
    correct_page_turns(result@.map(|i: int, x: i8| x as int), a@.map(|i: int, x: i8| x as int), m as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): Fixed type conversion issue by using ghost variable for spec mapping */
    let mut result = Vec::new();
    let mut s: i8 = 0;
    let mut i: usize = 0;
    
    let ghost a_spec = a@.map(|j: int, x: i8| x as int);
    
    while i < n as usize
        invariant
            n >= 1,
            m >= 1,
            a.len() == n as nat,
            a@ =~= a@,
            a_spec =~= a@.map(|j: int, x: i8| x as int),
            forall|j: int| 0 <= j < a.len() ==> a[j] >= 1,
            forall|j: int| 0 <= j < a_spec.len() ==> a_spec[j] >= 1,
            i <= n as nat,
            i <= a.len(),
            result.len() == i,
            0 <= s,
            s < m,
            s as int == compute_state_at(a_spec, m as int, i as int),
            forall|j: int| 0 <= j < i ==> {
                let state_j = compute_state_at(a_spec, m as int, j as int);
                #[trigger] result@[j] as int == (state_j + a_spec[j]) / (m as int)
            },
            forall|j: int| 0 <= j < result.len() ==> result[j] >= 0
    {
        proof {
            lemma_state_matches_loop(a_spec, m as int, i as nat, s as int);
        }
        
        let pages_today = a[i];
        let total = s + pages_today;
        let books_completed = total / m;
        let new_s = total % m;
        
        result.push(books_completed);
        
        proof {
            assert(result@[i as int] as int == books_completed as int);
            assert(books_completed as int == (s as int + pages_today as int) / (m as int));
            assert(s as int == compute_state_at(a_spec, m as int, i as int));
            assert(books_completed as int == (compute_state_at(a_spec, m as int, i as int) + a_spec[i as int]) / (m as int));
        }
        
        s = new_s;
        i = i + 1;
        
        proof {
            assert(s as int == (total % m) as int);
            assert(s as int == ((compute_state_at(a_spec, m as int, (i - 1) as int) + a_spec[(i - 1) as int]) % (m as int)));
            assert(s as int == compute_state_at(a_spec, m as int, i as int));
        }
    }
    
    proof {
        assert(result.len() == n as nat);
        assert(forall|j: int| 0 <= j < n ==> {
            let state_j = compute_state_at(a_spec, m as int, j as int);
            result@[j] as int == (state_j + a_spec[j]) / (m as int)
        });
    }
    
    result
}
// </vc-code>


}

fn main() {}