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

proof fn lemma_mod2_odd_even(x: int)
    ensures
        x % 2 == 1 || x % 2 == 0
{
}

proof fn lemma_odd_indices(a: Seq<int>)
    requires
        valid_input(a),
        a.len() % 2 == 1,
        a[a.len() - 1] % 2 == 1,
    ensures
        exists|k: int| 0 <= k < a.len() && a[k] % 2 == 1 && k % 2 == 0
{
    /* helper modified by LLM (iteration 4): Fixed index handling and type conversion */
    assert(0int % 2 == 0);
    
    if a[0] % 2 == 1 {
        assert(0int % 2 == 0);
        assert(0 <= 0 < a.len());
    } else {
        let mid: int = (a.len() as int) / 2;
        assert(mid % 2 == 0);
        assert(a[mid as nat] % 2 == 1);
        assert(0 <= mid < a.len() as int);
    }
}

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
    /* code modified by LLM (iteration 4): Fixed ghost code conversion from Vec to Seq */
    ghost {
        let a_spec = a@.map(|i, x| x as int);
        if can_be_divided(a_spec) {
            proof { lemma_odd_indices(a_spec); }
            return String::from_utf8(seq!['Y' as u8, 'e' as u8, 's' as u8]).unwrap();
        } else {
            return String::from_utf8(seq!['N' as u8, 'o' as u8]).unwrap();
        }
    }
    unreached()
}
// </vc-code>


}

fn main() {}