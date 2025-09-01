use vstd::prelude::*;

verus! {

// <vc-helpers>
/* No helpers needed */
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
    let mut res: Vec<i32> = Vec::new();
    let mut i: nat = 0;
    while i < input.len()
        invariant i <= input.len();
        invariant res@ == input@.slice(0, i).filter(|x: i32| x > 0);
        decreases input.len() - i;
    {
        let xi: i32 = input.index(i);
        if xi > 0 {
            let old_res_seq = res@;
            res.push(xi);
            proof {
                assert(res@ == old_res_seq + Seq::unit(xi));
                assert(input@.slice(0, i + 1).filter(|x: i32| x > 0)
                       == input@.slice(0, i).filter(|x: i32| x > 0) + Seq::unit(xi));
                assert(res@ == input@.slice(0, i + 1).filter(|x: i32| x > 0));
            }
        } else {
            proof {
                assert(input@.slice(0, i + 1) == input@.slice(0, i) + Seq::unit(xi));
                assert(Seq::unit(xi).filter(|x: i32| x > 0) == Seq::empty());
                assert(input@.slice(0, i + 1).filter(|x: i32| x > 0)
                       == input@.slice(0, i).filter(|x: i32| x > 0) + Seq::empty());
                assert(res@ == input@.slice(0, i + 1).filter(|x: i32| x > 0));
            }
        }
        i = i + 1;
    }
    res
}
// </vc-code>

fn main() {}
}