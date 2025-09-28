use vstd::prelude::*;

verus! {

// <vc-helpers>
proof fn update_elements_lemma(
    old_a: Seq<i32>,
    new_a: Seq<i32>,
) 
    requires
        old_a.len() >= 8,
        new_a.len() == old_a.len(),
        new_a[4] == old_a[4] + 3,
        new_a[7] == 516,
        forall|i: int| 0 <= i < old_a.len() ==> i != 7 && i != 4 ==> new_a[i] == old_a[i],
{
    assert forall|i: int| 0 <= i < old_a.len() implies (i != 7 && i != 4 implies new_a[i] == old_a[i]) by {
        if 0 <= i < old_a.len() && i != 7 && i != 4 {
            assert(new_a[i] == old_a[i]);
        }
    }
}

fn update_elements_helper(a: &mut Vec<i32>)
    requires 
        old(a).len() >= 8,
    ensures 
        old(a)[4] + 3 == a[4],
        a[7] == 516,
        forall|i: int| 0 <= i < a.len() ==> i != 7 && i != 4 ==> a[i] == old(a)[i],
        a.len() == old(a).len(),
{
    let old_val_4 = a[4];
    
    proof {
        assert(a@.len() == old(a)@.len());
        assert(0 <= 4 < a@.len());
        assert(0 <= 7 < a@.len());
        assert(old_val_4 == old(a)@[4]);
        assert(old_val_4 <= i32::MAX - 3);
    }
    
    a.set(4, old_val_4 + 3);
    a.set(7, 516);
    
    proof {
        assert(a@[4] == old_val_4 + 3);
        assert(a@[4] == old(a)@[4] + 3);
        assert(a@[7] == 516);
        assert forall|i: int| 0 <= i < old(a)@.len() implies (i != 7 && i != 4 implies a@[i] == old(a)@[i]) by {
            if 0 <= i < old(a)@.len() && i != 7 && i != 4 {
                assert(a@[i] == old(a)@[i]);
            }
        }
        
        update_elements_lemma(
            old(a)@,
            a@,
        );
    }
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
    update_elements_helper(a);
}
// </vc-code>

fn main() {}

}