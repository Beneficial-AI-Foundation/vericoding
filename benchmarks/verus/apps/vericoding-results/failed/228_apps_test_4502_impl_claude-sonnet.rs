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
/* helper modified by LLM (iteration 5): fixed type annotation for empty sequence in reverse_seq lemma */
proof fn lemma_compute_result_correct(a: Seq<int>)
    requires a.len() >= 1
    ensures compute_result(a) == simulate_operations(a)
    decreases a.len()
{
    if a.len() == 1 {
        assert(compute_result(a) == seq![a[0]]);
        assert(simulate_operations(a) == seq![a[0]]);
    } else {
        let shorter = a.subrange(0, (a.len() - 1) as int);
        lemma_compute_result_correct(shorter);
    }
}

proof fn lemma_reverse_seq_len(s: Seq<int>)
    ensures reverse_seq(s).len() == s.len()
    decreases s.len()
{
    if s.len() == 0 {
        assert(reverse_seq(s) == (seq![] as Seq<int>));
    } else {
        let rest = s.subrange(1, s.len() as int);
        lemma_reverse_seq_len(rest);
    }
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
{
    /* code modified by LLM (iteration 5): fixed ghost variables in proof blocks */
    proof {
        let n_int = n as int;
        let a_int = a@.map(|i: int, x: i8| x as int);
    }
    
    let o_len = if n % 2 == 0 { n / 2 } else { (n + 1) / 2 };
    let e_len = n / 2;
    
    let mut o = Vec::new();
    let mut e = Vec::new();
    
    let mut i: i8 = 0;
    while i < n
        invariant
            i <= n,
            o.len() == (i + 1) / 2,
            e.len() == i / 2,
            forall|j: int| 0 <= j < o.len() ==> o@[j] == a@[2*j],
            forall|j: int| 0 <= j < e.len() ==> e@[j] == a@[2*j + 1],
    {
        if i % 2 == 0 {
            o.push(a[i as usize]);
        } else {
            e.push(a[i as usize]);
        }
        i += 1;
    }
    
    e.reverse();
    o.reverse();
    
    let mut result = Vec::new();
    
    if n % 2 == 0 {
        result.append(&mut e);
        result.append(&mut o);
    } else {
        result.append(&mut o);
        result.append(&mut e);
    }
    
    result
}
// </vc-code>


}

fn main() {}