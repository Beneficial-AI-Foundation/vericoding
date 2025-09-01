use vstd::prelude::*;

verus! {

// <vc-helpers>
/* No helper lemmas needed for this implementation */
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
    let mut positive_list: Vec<i32> = Vec::new();
    let mut i: nat = 0;
    let n: nat = input.len();
    while i < n
        invariant i <= n;
        invariant positive_list@ == input@[0..i].filter(|x: i32| x > 0);
        decreases n - i
    {
        match input.get(i) {
            Some(v) => {
                let val: i32 = *v;
                if val > 0 {
                    // before push: positive_list@ == input@[0..i].filter(...)
                    positive_list.push(val);
                    // after push, we need to show the invariant for i+1
                    proof {
                        // input@[0..i+1] == input@[0..i] + seq![input@[i]]
                        assert(input@[0..i+1] == input@[0..i] + seq![input@[i]]);
                        // input@[i] equals val (from get(i) Some(v))
                        assert(input@[i] == val);
                        // therefore filtering the concatenation yields the concatenation of filters,
                        // and since val > 0 the filter of seq![val] is seq![val]
                        assert(input@[0..i+1].filter(|x: i32| x > 0) == input@[0..i].filter(|x: i32| x > 0) + seq![val]);
                        // combine with the previous invariant about positive_list@
                        assert(positive_list@ == input@[0..i+1].filter(|x: i32| x > 0));
                    }
                }
            }
            None => {}
        }
        i = i + 1;
    }
    proof {
        assert(i <= n);
        assert(!(i < n));
        assert(i == n);
        assert(positive_list@ == input@[0..i].filter(|x: i32| x > 0));
    }
    positive_list
}
// </vc-code>

fn main() {}
}