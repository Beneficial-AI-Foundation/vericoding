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
/* helper modified by LLM (iteration 5): added lemmas for string conversion proofs */
proof fn lemma_can_be_divided_equiv(a: Vec<i8>)
    requires valid_input(a@.map(|i, x| x as int))
    ensures
        can_be_divided(a@.map(|i, x| x as int)) <==> (
            a.len() % 2 == 1 && a[0] % 2 == 1 && a[a.len() - 1] % 2 == 1
        )
{
    let int_seq = a@.map(|i, x| x as int);
    assert(int_seq.len() == a.len());
    assert(int_seq[0] == a[0] as int);
    assert(int_seq[int_seq.len() - 1] == a[a.len() - 1] as int);
    assert((a[0] as int) % 2 == 1 <==> a[0] % 2 == 1);
    assert((a[a.len() - 1] as int) % 2 == 1 <==> a[a.len() - 1] % 2 == 1);
}

proof fn lemma_yes_string()
    ensures "Yes".to_string()@ =~= seq!['Y', 'e', 's']
{
}

proof fn lemma_no_string()
    ensures "No".to_string()@ =~= seq!['N', 'o']
{
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
    /* code modified by LLM (iteration 5): added string conversion proofs */
    let len = a.len();
    let first = a[0];
    let last = a[len - 1];
    
    proof {
        lemma_can_be_divided_equiv(a);
        lemma_yes_string();
        lemma_no_string();
    }
    
    if len % 2 == 1 && first % 2 == 1 && last % 2 == 1 {
        "Yes".to_string()
    } else {
        "No".to_string()
    }
}
// </vc-code>


}

fn main() {}