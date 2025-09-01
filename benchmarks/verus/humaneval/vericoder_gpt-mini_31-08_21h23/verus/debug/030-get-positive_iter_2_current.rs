use vstd::prelude::*;

verus! {

// <vc-helpers>
fn vec_of_positive(s: Seq<i32>) -> (v: Vec<i32>)
    ensures
        v@ == s.filter(|x: i32| x > 0)
{
    let mut v: Vec<i32> = Vec::new();
    let mut i: nat = 0;
    while i < s.len()
        invariant
            i <= s.len(),
            v@ == s.slice(0, i).filter(|x: i32| x > 0),
    {
        let x: i32 = s@[i];
        if x > 0 {
            v.push(x);
            // After push, v@ == old_v@ + seq![x], and old_v@ == s.slice(0,i).filter(...)
            assert(v@ == s.slice(0, i).filter(|y: i32| y > 0) + seq![x]);
            assert(s.slice(0, i+1).filter(|y: i32| y > 0) == s.slice(0, i).filter(|y: i32| y > 0) + seq![x]);
        } else {
            // No push: v@ unchanged and equals the filtered slice up to i+1
            assert(v@ == s.slice(0, i).filter(|y: i32| y > 0));
            assert(s.slice(0, i+1).filter(|y: i32| y > 0) == s.slice(0, i).filter(|y: i32| y > 0));
        }
        i = i + 1;
    }
    v
}
// </vc-helpers>

// <vc-spec>
fn get_positive(input: Vec<i32>) -> (positive_list: Vec<i32>)
    // post-conditions-start
    ensures
        positive_list@ == input@.filter(|x: i32| x > 0),
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    vec_of_positive(input@)
}
// </vc-code>

fn main() {}
}