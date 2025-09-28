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
/* helper modified by LLM (iteration 5): added reverse_vec helper to fix reverse implementation in main code */
fn reverse_vec(v: &Vec<i8>) -> (result: Vec<i8>)
    requires v.len() as int >= 0,
    ensures result@.map(|i: int, x: i8| x as int) == reverse_seq(v@.map(|i: int, x: i8| x as int)),
{
    let mut res: Vec<i8> = Vec::new();
    let mut i: usize = 0;
    while i < v.len()
        invariant
            0 <= i as int <= v.len() as int,
            res@.len() as int == i as int,
        decreases v.len() as int - i as int,
    {
        res.push(v[v.len() - 1 - i]);
        i = i + 1;
    }
    res
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
/* code modified by LLM (iteration 5): used i as int in invariants to fix verification, added call to reverse_vec helper */
{
    let mut o_vec: Vec<i8> = Vec::new();
    let mut e_vec: Vec<i8> = Vec::new();
    let nn: usize = n as usize;
    let mut i: usize = 0;
    while i < nn
        invariant
            0 <= i as int <= nn as int,
            o_vec@.len() as int == (i as int + 1) / 2,
            e_vec@.len() as int == i as int - o_vec@.len() as int,
        decreases nn as int - i as int,
    {
        if i % 2 == 0 {
            o_vec.push(a[i]);
        } else {
            e_vec.push(a[i]);
        }
        i = i + 1;
    }
    let rev_o: Vec<i8> = reverse_vec(&o_vec);
    let rev_e: Vec<i8> = reverse_vec(&e_vec);
    let mut result: Vec<i8> =
        if nn % 2 == 0 {
            rev_e
        } else {
            rev_o
        };
    let to_add: Vec<i8> =
        if nn % 2 == 0 {
            o_vec
        } else {
            e_vec
        };
    result.extend(to_add);
    result
}
// </vc-code>


}

fn main() {}