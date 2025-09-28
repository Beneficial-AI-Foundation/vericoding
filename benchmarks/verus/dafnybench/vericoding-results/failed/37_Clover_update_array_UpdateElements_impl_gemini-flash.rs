use vstd::prelude::*;

verus! {

// <vc-helpers>
#[macro_export]
macro_rules! assert_vec_eq {
    ($vec1:expr, $vec2:expr) => {
        #[verifier::proof]
        {
            assert($vec1.len() == $vec2.len());
            let mut i = 0;
            while i < $vec1.len()
                invariant
                    i <= $vec1.len(),
                    forall|j: int| 0 <= j < i ==> $vec1.view()@[j] == $vec2.view()@[j],
            {
                assert($vec1.view()@[i] == $vec2.view()@[i]);
                i += 1;
            }
        }
    };
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
    let old_a_len = old(a).len();
    let old_a_view = old(a).view();

    let fourth_element_old = a.get(4);
    assert(fourth_element_old.is_Some()); // This is fine, OptionAdditionalFns::is_Some is deprecated for matches! but not wrong.
    let four_element_val = fourth_element_old.unwrap();
    
    a.set(4, four_element_val + 3);
    a.set(7, 516);

    proof {
        assert(a.len() == old_a_len);
        assert(a.view()@[4] == old_a_view@[4] + 3);
        assert(a.view()@[7] == 516);
        
        let mut i = 0;
        while i < old_a_len
            invariant
                i <= old_a_len,
                a.len() == old_a_len,
                forall|j: int| 
                    0 <= j < i && j != 4 && j != 7 ==> a.view()@[j] == old_a_view@[j],
                a.view()@[4] == old_a_view@[4] + 3,
                a.view()@[7] == 516,
        {
            if i != 4 && i != 7 {
                assert(a.view()@[i] == old_a_view@[i]);
            }
            i += 1;
        }
    }
}
// </vc-code>

fn main() {}

}