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
/* helper modified by LLM (iteration 5): Fixed type mismatches in Seq::new calls and invariants */
proof fn lemma_simulate_equals_compute(a: Seq<int>)
    requires
        a.len() >= 1,
    ensures
        simulate_operations(a) == compute_result(a),
    decreases a.len()
{
    if a.len() == 1 {
        assert(simulate_operations(a) == seq![a[0]]);
        assert(compute_result(a) == seq![a[0]]);
    } else {
        let n = a.len();
        let shorter = a.subrange(0, (n - 1) as int);
        lemma_simulate_equals_compute(shorter);
        
        assert(simulate_operations(a) == reverse_seq(simulate_operations(shorter).push(a[(n - 1) as int])));
        
        if n % 2 == 0 {
            let o_full = Seq::new(n / 2, |i: int| a[2*i]);
            let e_full = Seq::new(n / 2, |i: int| a[2*i + 1]);
            let o_short = Seq::new(((n - 1) / 2) as nat, |i: int| shorter[2*i]);
            let e_short = Seq::new(((n - 1) / 2) as nat, |i: int| shorter[2*i + 1]);
            
            assert(o_full == o_short.push(a[n - 2]));
            assert(e_full == e_short.push(a[n - 1]));
            assert(compute_result(a) == reverse_seq(e_full).add(o_full));
        } else {
            let o_full = Seq::new((n + 1) / 2, |i: int| a[2*i]);
            let e_full = Seq::new(n / 2, |i: int| a[2*i + 1]);
            let o_short = Seq::new(n / 2, |i: int| shorter[2*i]);
            let e_short = Seq::new(((n - 1) / 2) as nat, |i: int| shorter[2*i + 1]);
            
            assert(o_full == o_short.push(a[n - 1]));
            assert(e_full == e_short);
            assert(compute_result(a) == reverse_seq(o_full).add(e_full));
        }
    }
}

fn reverse_vec(v: Vec<i8>) -> (result: Vec<i8>)
    ensures
        result.len() == v.len(),
        result@.map(|i: int, x: i8| x as int) == reverse_seq(v@.map(|i: int, x: i8| x as int)),
{
    let mut result = Vec::new();
    let mut i = v.len();
    
    while i > 0
        invariant
            i <= v.len(),
            result.len() == v.len() - i,
            result@.map(|j: int, x: i8| x as int) == reverse_seq(v@.subrange(i as int, v.len() as int).map(|j: int, x: i8| x as int)),
        decreases i
    {
        i = i - 1;
        result.push(v[i]);
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
{
    /* code modified by LLM (iteration 5): Fixed type conversion in invariant conditional */
    let n_usize = n as usize;
    
    proof {
        let a_int = a@.map(|i: int, x: i8| x as int);
        lemma_simulate_equals_compute(a_int);
    }
    
    let mut odd_vec = Vec::new();
    let mut even_vec = Vec::new();
    
    let mut i: usize = 0;
    while i < n_usize
        invariant
            i <= n_usize,
            odd_vec.len() == (if i % 2 == 0 { i / 2 } else { (i + 1usize) / 2 }),
            even_vec.len() == i / 2,
            forall|j: int| 0 <= j < odd_vec.len() ==> odd_vec[j] == a[2 * j],
            forall|j: int| 0 <= j < even_vec.len() ==> even_vec[j] == a[2 * j + 1],
        decreases n_usize - i
    {
        if i % 2 == 0 {
            odd_vec.push(a[i]);
        } else {
            even_vec.push(a[i]);
        }
        i = i + 1;
    }
    
    let result = if n_usize % 2 == 0 {
        let reversed_even = reverse_vec(even_vec);
        let mut result = reversed_even;
        let mut j: usize = 0;
        while j < odd_vec.len()
            invariant
                j <= odd_vec.len(),
                result.len() == even_vec.len() + j,
                forall|k: int| 0 <= k < even_vec.len() ==> result[k] == reversed_even[k],
                forall|k: int| 0 <= k < j ==> result[(even_vec.len() + k) as int] == odd_vec[k],
            decreases odd_vec.len() - j
        {
            result.push(odd_vec[j]);
            j = j + 1;
        }
        result
    } else {
        let reversed_odd = reverse_vec(odd_vec);
        let mut result = reversed_odd;
        let mut j: usize = 0;
        while j < even_vec.len()
            invariant
                j <= even_vec.len(),
                result.len() == odd_vec.len() + j,
                forall|k: int| 0 <= k < odd_vec.len() ==> result[k] == reversed_odd[k],
                forall|k: int| 0 <= k < j ==> result[(odd_vec.len() + k) as int] == even_vec[k],
            decreases even_vec.len() - j
        {
            result.push(even_vec[j]);
            j = j + 1;
        }
        result
    };
    
    result
}
// </vc-code>


}

fn main() {}