// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(a: Seq<int>) -> bool {
    a.len() >= 1
}

spec fn can_be_divided(a: Seq<int>) -> bool
    recommends valid_input(a)
{
    a.len() % 2 == 1 && a[0] % 2 == 1 && a[a.len() - 1] % 2 == 1
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn solve(a: Vec<i8>) -> (result: String)
    requires 
        valid_input(a@.map(|i, x| x as int)),
    ensures 
        can_be_divided(a@.map(|i, x| x as int)) ==> result@ =~= seq!['Y', 'e', 's'],
        (!can_be_divided(a@.map(|i, x| x as int))) ==> result@ =~= seq!['N', 'o'],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): added proof block to show equivalence between computed condition and spec function */
    let n = a.len();
    let len_odd = n % 2 == 1;
    let first = a[0] as int;
    let last = a[n-1] as int;
    let first_odd = first % 2 == 1;
    let last_odd = last % 2 == 1;
    let cond = len_odd && first_odd && last_odd;

    proof {
        assert(can_be_divided(a@.map(|i, x| x as int)) == 
               (a@.map(|i, x| x as int).len() % 2 == 1 && 
                a@.map(|i, x| x as int)[0] % 2 == 1 && 
                a@.map(|i, x| x as int)[a@.map(|i, x| x as int).len()-1] % 2 == 1));
        assert(a@.map(|i, x| x as int).len() == n);
        assert(a@.map(|i, x| x as int)[0] == first);
        assert(a@.map(|i, x| x as int)[n-1] == last);
        assert(can_be_divided(a@.map(|i, x| x as int)) == (n % 2 == 1 && first % 2 == 1 && last % 2 == 1));
        assert(can_be_divided(a@.map(|i, x| x as int)) == cond);
    }

    if cond {
        "Yes".to_string()
    } else {
        "No".to_string()
    }
}
// </vc-code>


}

fn main() {}