use vstd::prelude::*;

verus! {

// <vc-helpers>
#[verifier(external_body)]
#[verifier(broadcast_forall)]
pub proof fn lemma_int_mod_2_auto_spec(n: int)
    ensures
        (n % 2 == 0) <==> (n % 2 == 0),
{
}
// </vc-helpers>

// <vc-spec>
fn is_even(n: int) -> (result: bool)
    ensures result <==> n % 2 == 0
// </vc-spec>
// <vc-code>
{
    let zero: int = 0int();
    let two: int = 2int();

    proof {
        lemma_int_mod_2_auto_spec(n);
    }
    if n % two == zero {
        true
    } else {
        false
    }
}
// </vc-code>

fn main() {
}

}