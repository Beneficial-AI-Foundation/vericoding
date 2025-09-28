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
/* helper modified by LLM (iteration 2): added helper to unfold state computation */
proof fn lemma_state_unfold(a: Seq<int>, m: int, i: int)
    requires
        m >= 1,
        0 <= i < a.len(),
    ensures
        compute_state_at(a, m, i + 1) == (compute_state_at(a, m, i) + a[i]) % m,
{
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
    /* code modified by LLM (iteration 2): fixed ghost variable declarations and moved ghost code into proof blocks */
    let mut result: Vec<i8> = Vec::new();
    let mut i: i8 = 0;
    let mut s: i8 = 0;

    let ghost m_int = m as int;
    let ghost a_spec = a@.map(|i: int, x: i8| x as int);

    proof {
        assert(compute_state_at(a_spec, m_int, 0) == 0);
    }

    while i < n
        invariant
            valid_input(n as int, m as int, a_spec),
            a_spec == a@.map(|i, x| x as int),
            m_int == m as int,
            0 <= i <= n,
            result@.len() == i as nat,
            0 <= s < m,
            s as int == compute_state_at(a_spec, m_int, i as int),
            forall|j: int| 0 <= j < i as int ==> {
                let state_j = compute_state_at(a_spec, m_int, j);
                #[trigger] result@[j] as int == (state_j + a_spec[j]) / m_int
            },
            forall|j: int| 0 <= j < i as int ==> result@[j] >= 0,
        decreases n - i
    {
        let current_a = a[i as usize] as i32;
        let current_s = s as i32;
        let m_i32 = m as i32;

        let total_pages = current_s + current_a;
        let page_turns_i32 = total_pages / m_i32;

        assert(page_turns_i32 >= 0);
        assert(page_turns_i32 <= 127);

        let page_turns = page_turns_i32 as i8;
        result.push(page_turns);

        let next_s_i32 = total_pages % m_i32;
        assert(0 <= next_s_i32 < m_i32);
        
        let next_s = next_s_i32 as i8;
        
        proof {
            lemma_state_unfold(a_spec, m_int, i as int);
        }
        
        s = next_s;
        i = i + 1;
    }
    result
}
// </vc-code>


}

fn main() {}