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
/* helper modified by LLM (iteration 5): relate runtime parity checks to spec predicate */
fn lemma_can_be_divided_equiv(a: &Vec<i8>)
    requires
        valid_input(a@.map(|i, x| x as int)),
    ensures
        (a.len() % 2 == 1 && (a[0] as i32) % 2 == 1 && (a[a.len() - 1] as i32) % 2 == 1) == can_be_divided(a@.map(|i, x| x as int)),
{
    proof {
        let seq = a@.map(|i, x| x as int);
        // lengths correspond
        assert(seq.len() == a.len() as nat);
        // parity of lengths agree
        assert((a.len() % 2 == 1) == (seq.len() % 2 == 1));
        // parity of first element agree
        assert(((a[0] as i32) % 2 == 1) == (seq[0] % 2 == 1));
        // parity of last element agree
        assert(((a[a.len() - 1] as i32) % 2 == 1) == (seq[seq.len() - 1] % 2 == 1));
        // unfold can_be_divided on seq
        assert(can_be_divided(seq) == (seq.len() % 2 == 1 && seq[0] % 2 == 1 && seq[seq.len() - 1] % 2 == 1));
        // combine to reach the claimed equivalence
        assert((a.len() % 2 == 1 && (a[0] as i32) % 2 == 1 && (a[a.len() - 1] as i32) % 2 == 1) == can_be_divided(seq));
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
    /* code modified by LLM (iteration 5): compute parity and construct string via vstd helper */
    let cond = a.len() % 2 == 1 && (a[0] as i32) % 2 == 1 && (a[a.len() - 1] as i32) % 2 == 1;
    let result = if cond {
        vstd::string::string_from_seq(seq!['Y','e','s'])
    } else {
        vstd::string::string_from_seq(seq!['N','o'])
    };
    proof {
        lemma_can_be_divided_equiv(&a);
        assert(can_be_divided(a@.map(|i, x| x as int)) == cond);
        if cond {
            assert(result@ =~= seq!['Y','e','s']);
        } else {
            assert(result@ =~= seq!['N','o']);
        }
    }
    result
}
// </vc-code>


}

fn main() {}