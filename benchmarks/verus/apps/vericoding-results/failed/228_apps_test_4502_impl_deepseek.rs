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
proof fn lemma_reverse_push(s: Seq<int>, x: int)
    requires
        s.len() >= 0,
    ensures
        reverse_seq(s.push(x)) == seq![x].add(reverse_seq(s)),
decreases s.len() when s.len() > 0
{
    if s.len() == 0 {
        assert(reverse_seq(Seq::<int>::empty().push(x)) == seq![x]);
        assert(seq![x].add(reverse_seq(s)) == seq![x]);
    } else {
        lemma_reverse_push(s.subrange(1, s.len() as int), x);
    }
}

proof fn lemma_simulate_equals_compute(a: Seq<int>)
    requires
        a.len() >= 1,
    ensures
        simulate_operations(a) == compute_result(a),
    decreases a.len() when a.len() > 0
{
    if a.len() == 1 {
        assert(compute_result(a) == seq![a[0]]);
    } else {
        let shorter = a.subrange(0, (a.len() - 1) as int);
        lemma_simulate_equals_compute(shorter);
        let prev = simulate_operations(shorter);
        lemma_reverse_push(prev, a[(a.len() - 1) as int]);
        assert(reverse_seq(prev.push(a[(a.len() - 1) as int])) == seq![a[(a.len() - 1) as int]].add(reverse_seq(prev)));
        assert(compute_result(a) == if a.len() % 2 == 0 { reverse_seq(Seq::new(a.len() / 2, |i: int| a[2*i + 1])).add(Seq::new(a.len() / 2, |i: int| a[2*i])) } else { reverse_seq(Seq::new((a.len() + 1) / 2, |i: int| a[2*i])).add(Seq::new(a.len() / 2, |i: int| a[2*i + 1])) });
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
    /* code modified by LLM (iteration 5): Fix compilation error by using ghost variable for n_int */
    ghost {
        let n_int = n as int;
    }
    let mut result: Vec<i8> = Vec::with_capacity(n as usize);
    let mut i: usize = 0;
    let mut j: usize = (n as usize) - 1;
    
    while i <= j {
        if i == j {
            result.push(a[i]);
            i += 1;
        } else {
            result.push(a[i]);
            result.push(a[j]);
            i += 1;
            j -= 1;
        }
    }
    
    result
}
// </vc-code>


}

fn main() {}