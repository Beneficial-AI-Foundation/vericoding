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
/* helper modified by LLM (iteration 5): convert Vec<i8> to Seq<int> */
spec fn vec_to_seq_i8(v: Vec<i8>) -> Seq<int> {
    v@.map(|i: int, x: i8| x as int)
}

/* helper modified by LLM (iteration 5): prove runtime Vec length equals ghost view len and matches n */
proof fn vec_len_matches_n(n: i8, v: Vec<i8>)
    requires
        valid_input(n as int, v@.map(|i: int, x: i8| x as int)),
{
    assert(v@.len() == n as int);
    assert(v.len() == (v@.len() as usize));
    assert(v.len() == (n as usize));
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
    /* code modified by LLM (iteration 5): construct result matching compute_result with verified bounds */
    let n_usize: usize = n as usize;

    proof {
        vec_len_matches_n(n, a);
    }

    let mut result: Vec<i8> = Vec::new();

    if n_usize % 2 == 0 {
        let m: usize = n_usize / 2;

        let mut t: usize = 0;
        while t < m
            invariant
                t <= m,
                result.len() == t,
                a.len() == n_usize,
            decreases m - t
        {
            let idx_int: int = (n_usize as int) - 1 - 2*(t as int);
            proof {
                assert(t < m);
                assert(2*(m as int) == n_usize as int);
                assert(2*(t as int) <= (n_usize as int) - 2);
                assert(idx_int >= 0);
                assert(idx_int < (n_usize as int));
            }
            let idx: usize = idx_int as usize;
            result.push(a[idx]);
            t += 1;
        }

        let mut i: usize = 0;
        while i < m
            invariant
                i <= m,
                result.len() == m + i,
                a.len() == n_usize,
            decreases m - i
        {
            let idx_int: int = 2*(i as int);
            proof {
                assert(idx_int >= 0);
                assert(idx_int < (n_usize as int));
            }
            let idx: usize = idx_int as usize;
            result.push(a[idx]);
            i += 1;
        }
    } else {
        let m: usize = n_usize / 2; // floor

        let mut t: usize = 0;
        while t < (m + 1)
            invariant
                t <= m + 1,
                result.len() == t,
                a.len() == n_usize,
            decreases (m + 1) - t
        {
            let idx_int: int = 2*((m as int) - (t as int));
            proof {
                assert((m as int) - (t as int) >= 0);
                assert(idx_int >= 0);
                assert(idx_int < (n_usize as int));
            }
            let idx: usize = idx_int as usize;
            result.push(a[idx]);
            t += 1;
        }

        let mut i: usize = 0;
        while i < m
            invariant
                i <= m,
                result.len() == (m + 1) + i,
                a.len() == n_usize,
            decreases m - i
        {
            let idx_int: int = 2*(i as int) + 1;
            proof {
                assert(idx_int >= 0);
                assert(idx_int < (n_usize as int));
            }
            let idx: usize = idx_int as usize;
            result.push(a[idx]);
            i += 1;
        }
    }

    result
}

// </vc-code>


}

fn main() {}