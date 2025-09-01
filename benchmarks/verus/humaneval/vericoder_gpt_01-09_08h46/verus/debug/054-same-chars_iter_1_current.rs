use vstd::hash_set::HashSetWithView;
use vstd::prelude::*;
use vstd::std_specs::hash::axiom_u8_obeys_hash_table_key_model;

verus! {

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
#[verifier::loop_isolation(false)]
fn same_chars(s0: &Vec<u8>, s1: &Vec<u8>) -> (same: bool)
    // post-conditions-start
    ensures
        same <==> (forall|i: int| #![auto] 0 <= i < s0.len() ==> s1@.contains(s0[i])) && (forall|
            i: int,
        |
            #![auto]
            0 <= i < s1.len() ==> s0@.contains(s1[i])),
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    let mut ok1: bool = true;
    let mut i: usize = 0;
    while i < s0.len()
        invariant 0 <= i <= s0.len()
        invariant ok1 == (forall|idx: int| 0 <= idx < i as int ==> #[trigger] s1@.contains(s0[idx as usize]))
        decreases s0.len() - i
    {
        let i0 = i;
        let a = s0[i0];
        let mut found: bool = false;
        let mut j: usize = 0;
        while j < s1.len()
            invariant 0 <= j <= s1.len()
            invariant found == (exists|k: int| 0 <= k < j as int && s1[k as usize] == a)
            decreases s1.len() - j
        {
            if s1[j] == a {
                found = true;
            }
            j += 1;
        }
        assert(found == (exists|k:int| 0 <= k < s1.len() && s1[k as usize] == a));
        assert(s1@.contains(a) == (exists|k:int| 0 <= k < s1.len() && s1[k as usize] == a));

        let ok1_prev = ok1;
        ok1 = ok1_prev && found;
        i = i0 + 1;

        proof {
            assert(
                (forall|idx:int| 0 <= idx < i as int ==> #[trigger] s1@.contains(s0[idx as usize]))
                <=>
                ((forall|idx:int| 0 <= idx < i0 as int ==> #[trigger] s1@.contains(s0[idx as usize]))
                 && s1@.contains(s0[i0]))
            );
        }
    }

    let mut ok2: bool = true;
    let mut i2: usize = 0;
    while i2 < s1.len()
        invariant 0 <= i2 <= s1.len()
        invariant ok2 == (forall|idx: int| 0 <= idx < i2 as int ==> #[trigger] s0@.contains(s1[idx as usize]))
        decreases s1.len() - i2
    {
        let i20 = i2;
        let a2 = s1[i20];
        let mut found2: bool = false;
        let mut j2: usize = 0;
        while j2 < s0.len()
            invariant 0 <= j2 <= s0.len()
            invariant found2 == (exists|k: int| 0 <= k < j2 as int && s0[k as usize] == a2)
            decreases s0.len() - j2
        {
            if s0[j2] == a2 {
                found2 = true;
            }
            j2 += 1;
        }
        assert(found2 == (exists|k:int| 0 <= k < s0.len() && s0[k as usize] == a2));
        assert(s0@.contains(a2) == (exists|k:int| 0 <= k < s0.len() && s0[k as usize] == a2));

        let ok2_prev = ok2;
        ok2 = ok2_prev && found2;
        i2 = i20 + 1;

        proof {
            assert(
                (forall|idx:int| 0 <= idx < i2 as int ==> #[trigger] s0@.contains(s1[idx as usize]))
                <=>
                ((forall|idx:int| 0 <= idx < i20 as int ==> #[trigger] s0@.contains(s1[idx as usize]))
                 && s0@.contains(s1[i20]))
            );
        }
    }

    let same = ok1 && ok2;
    same
}
// </vc-code>

fn main() {}
}