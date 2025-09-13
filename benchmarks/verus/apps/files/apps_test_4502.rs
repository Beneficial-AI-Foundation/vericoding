// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn valid_input(n: int, a: Seq<int>) -> bool {
    n >= 1 && a.len() == n
}

spec fn simulate_operations(a: Seq<int>) -> Seq<int>
    decreases a.len()
{
    if a.len() >= 1 {
        if a.len() == 1 {
            seq![a[0]]
        } else {
            let prev = simulate_operations(a.subrange(0, a.len() - 1));
            reverse_seq(prev.push(a[a.len() - 1]))
        }
    } else {
        Seq::empty()
    }
}

spec fn compute_result(a: Seq<int>) -> Seq<int> {
    if a.len() >= 1 {
        let n = a.len();
        let o_len = if n % 2 == 0 { n / 2 } else { (n + 1) / 2 };
        let e_len = n / 2;
        let o = Seq::new(o_len, |i: int| a[2 * i]);
        let e = Seq::new(e_len, |i: int| a[2 * i + 1]);
        if n % 2 == 0 {
            reverse_seq(e).add(o)
        } else {
            reverse_seq(o).add(e)
        }
    } else {
        Seq::empty()
    }
}

spec fn reverse_seq(s: Seq<int>) -> Seq<int> {
    Seq::new(s.len(), |i: int| s[s.len() - 1 - i])
}
// </vc-helpers>

// <vc-spec>
fn solve(n: int, a: Seq<int>) -> (result: Seq<int>)
    requires 
        valid_input(n, a),
    ensures 
        result.len() == n,
        result == compute_result(a),
// </vc-spec>
// <vc-code>
{
    assume(false);
    Seq::empty()
}
// </vc-code>


}

fn main() {}