use vstd::prelude::*;

verus! {

// <vc-helpers>
// No updates needed for helpers in this case
// </vc-helpers>

// <vc-spec>
// <vc-spec>
fn find_position_of_element(a: &[i32], element: usize, n1: usize, s1: Seq<i32>) -> (result: (i32, usize))
    requires
        n1 == s1.len() && 0 <= n1 <= a.len(),
        forall|i: int| 0 <= i < s1.len() ==> a[i] == s1[i],
    ensures
        result.0 == -1 || result.0 >= 1,
        s1.len() != 0 && result.0 >= 1 ==> exists|i: int| 0 <= i < s1.len() && s1[i] == element,
// </vc-spec>
// </vc-spec>

// <vc-code>
fn find_position_of_element(a: &[i32], element: usize, n1: usize, s1: Seq<i32>) -> (result: (i32, usize))
    requires
        n1 == s1.len(),
        0 <= n1 <= a.len(),
        forall|i: int| 0 <= i < s1.len() ==> a[i] == s1[i],
    ensures
        result.0 == -1 || result.0 >= 1,
        s1.len() != 0 && result.0 >= 1 ==> exists|i: int| 0 <= i < s1.len() && s1[i] == element as i32,
{
    if s1.len() == 0 {
        (-1, 0)
    } else {
        let mut i: usize = 0;
        while i < n1
            invariant
                0 <= i <= n1,
                n1 == s1.len(),
                forall|k: int| 0 <= k < i ==> s1[k] != element as i32,
        {
            if s1[i] == element as i32 {
                return ((i as i32) + 1, element);
            }
            i = i + 1;
        }
        (-1, 0)
    }
}
// </vc-code>

fn main() {}

}