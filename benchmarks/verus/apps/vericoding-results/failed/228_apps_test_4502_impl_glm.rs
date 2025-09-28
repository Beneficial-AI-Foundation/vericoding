// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(n: int, a: Seq<int>) -> bool {
    n >= 1 && a.len() == n
}

spec fn simulate_operations(a: Seq<int>) -> Seq<int>
    recommends a.len() >= 1
    decreases a.len() when a.len() > 0
{
    if a.len() == 1 {
        seq![a[0]]
    } else {
        let shorter = a.subrange(0, (a.len() - 1) as int);
        let prev = simulate_operations(shorter);
        reverse_seq(prev.push(a[(a.len() - 1) as int]))
    }
}

spec fn compute_result(a: Seq<int>) -> Seq<int>
    recommends a.len() >= 1
{
    let n = a.len();
    let o = Seq::new(if n % 2 == 0 { n / 2 } else { (n + 1) / 2 }, |i: int| a[2*i]);
    let e = Seq::new(n / 2, |i: int| a[2*i + 1]);
    if n % 2 == 0 {
        reverse_seq(e).add(o)
    } else {
        reverse_seq(o).add(e)
    }
}

spec fn reverse_seq(s: Seq<int>) -> Seq<int>
    decreases s.len() when s.len() > 0
{
    if s.len() == 0 {
        seq![]
    } else {
        let rest = s.subrange(1, s.len() as int);
        reverse_seq(rest).push(s[0])
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): Fixed move errors by combining conditionals into a single assignment */
fn compute_result_vec(a: Vec<i8>) -> (result: Vec<i8>)
    requires
        a@.map(|i: int, x: i8| x as int).len() >= 1,
    ensures
        result.len() == a@.map(|i: int, x: i8| x as int).len(),
        result@.map(|i: int, x: i8| x as int) == compute_result(a@.map(|i: int, x: i8| x as int)),
{
    let n = a.len();
    let mut o_vec = Vec::new();
    let mut e_vec = Vec::new();
    let mut i = 0usize;
    while i < n
        invariant
            i <= n,
            o_vec.len() == (i as nat + 1) / 2,
            e_vec.len() == (i as nat) / 2,
        decreases n - i
    {
        if i % 2 == 0 {
            o_vec.push(a[i]);
        } else {
            e_vec.push(a[i]);
        }
        i += 1;
    }

    let (vec_to_reverse, other_vec) = if n % 2 == 0 { (e_vec, o_vec) } else { (o_vec, e_vec) };

    let mut rev = Vec::new();
    let mut j = vec_to_reverse.len();
    while j > 0
        invariant
            j <= vec_to_reverse.len(),
            rev.len() == (vec_to_reverse.len() - j) as nat,
            forall|k: int| 0 <= k < rev.len() ==> rev@[k] == vec_to_reverse@[vec_to_reverse.len() - 1 - k],
        decreases j
    {
        j -= 1;
        rev.push(vec_to_reverse[j]);
    }

    let mut result = rev;
    let mut k = 0usize;
    while k < other_vec.len()
        invariant
            k <= other_vec.len(),
            result.len() == rev.len() + k as nat,
        decreases other_vec.len() - k
    {
        result.push(other_vec[k]);
        k += 1;
    }

    result
}
// </vc-helpers>

// <vc-spec>
fn solve(n: i8, a: Vec<i8>) -> (result: Vec<i8>)
    requires 
        valid_input(n as int, a@.map(|i: int, x: i8| x as int)),
    ensures 
        result.len() == n as int,
        result@.map(|i: int, x: i8| x as int) == compute_result(a@.map(|i: int, x: i8| x as int)),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 3): Call helper function to compute result */
{
    compute_result_vec(a)
}
// </vc-code>


}

fn main() {}