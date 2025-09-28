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
/* helper modified by LLM (iteration 5): [Corrected the type annotation for `1` and `0` in the `if` expression to `1int` and `0int`, respectively, to resolve the type inference error. This ensures that the literal values are treated as integers, which is required for the arithmetic operations.] */
spec fn calculate_next_arr_len(n_local: int, i: int, j: int) -> nat
{
    if j < 0 {
        (i / 2) as nat
    } else {
        ((i as int / 2) + (if n_local % 2 == 0 { (n_local - 1 - j) / 2 } else { (n_local - 2 - j) / 2 } ) + ( if j % 2 == 0 {1int} else {0int} )) as nat
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
    /* code modified by LLM (iteration 5): [Replaced the direct calculation of `next_arr.len()` in the second `while` loop's invariant with a call to the `calculate_next_arr_len` helper function. This simplifies the invariant and makes it more readable, leveraging the logic encapsulated in the helper.] */
    let mut arr = a.clone();
    let mut n_local = n;

    while n_local > 1
        invariant
            1 <= n_local,
            n_local <= n,
            arr.len() == n_local as usize,
            arr@.map(|i, x: i8| x as int) == compute_result(a@.map(|i, x: i8| x as int).subrange(0, n_local as int)),
        decreases n_local
    {
        let mut next_arr: Vec<i8> = Vec::new();
        let mut i: i8 = 0;
        while i < n_local
            invariant
                0 <= i,
                i <= n_local,
                next_arr.len() == (i as int / 2) as usize,
                arr.len() == n_local as usize,
                n_local >= 1
            decreases n_local - i
        {
            next_arr.push(arr[i as usize]);
            i += 2;
        }

        let mut j: i8 = if n_local % 2 == 0 { n_local - 1 } else { n_local - 2 };
        while j >= 0 && j < n_local
            invariant
                -1 <= j,
                j < n_local,
                next_arr.len() == calculate_next_arr_len(n_local as int, i as int, j as int) as usize,
                arr.len() == n_local as usize,
                n_local >= 1
            decreases j
        {
            next_arr.push(arr[j as usize]);
            j = j - 2;
        }

        arr = next_arr;
        n_local = arr.len() as i8;
    }

    arr
}
// </vc-code>


}

fn main() {}