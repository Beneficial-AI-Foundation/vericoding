use vstd::prelude::*;

verus! {

// <vc-helpers>
proof fn update_fourth_proof(a: Seq<i32>, a_prime: Seq<i32>)
    requires
        a.len() >= 8,
        a_prime.len() == a.len(),
        a_prime[4] == a[4] + 3,
        a_prime[7] == 516,
        forall|i: int| 0 <= i < a.len() ==> i != 7 && i != 4 ==> a_prime[i] == a[i]
    ensures
        a[4] + 3 == a_prime[4],
        a_prime[7] == 516
{
}
// </vc-helpers>

// <vc-spec>
fn update_elements(a: &mut Vec<i32>)
    requires 
        old(a).len() >= 8,
    ensures 
        old(a)[4] + 3 == a[4],
        a[7] == 516,
        forall|i: int| 0 <= i < a.len() ==> i != 7 && i != 4 ==> a[i] == old(a)[i],
        a.len() == old(a).len(),
// </vc-spec>
// <vc-code>
{
    let old_a_spec = a@;
    proof {
        assert(old_a_spec.len() >= 8);
    }
    
    if a.len() >= 8 {
        a[4] = a[4] + 3;
        a[7] = 516;
        
        proof {
            let new_a_spec = a@;
            assert(new_a_spec.len() == old_a_spec.len());
            assert(new_a_spec[4] == old_a_spec[4] + 3);
            assert(new_a_spec[7] == 516);
            assert forall|i: int| 0 <= i < new_a_spec.len() implies i != 7 && i != 4 ==> new_a_spec[i] == old_a_spec[i] by {
                if (0 <= i < new_a_spec.len() && i != 7 && i != 4) {
                    assert(new_a_spec[i] == old_a_spec[i]);
                }
            }
            update_fourth_proof(old_a_spec, new_a_spec);
        }
    }
}
// </vc-code>

fn main() {}

}