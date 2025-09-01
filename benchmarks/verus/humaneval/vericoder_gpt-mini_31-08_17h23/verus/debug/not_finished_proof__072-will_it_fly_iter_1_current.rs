use vstd::prelude::*;

verus! {

// pure-end

spec fn spec_sum(s: Seq<u32>) -> (ret:int) {
    s.fold_left(0, |x: int, y| x + y)
}
// pure-end

// <vc-helpers>
// <vc-helpers>
proof fn spec_sum_prefix_step(s: Seq<u32>, i: nat)
    requires i < s.len()
    ensures spec_sum(s.slice(0, i + 1)) == spec_sum(s.slice(0, i)) + s@[i]
{
    // Proof by induction on i
    if i == 0 {
        // slice(0,0) is empty, slice(0,1) is single element
        assert(s.slice(0, 0).len() == 0);
        assert(spec_sum(s.slice(0, 0)) == 0);
        assert(s.slice(0, 1).len() == 1);
        assert(spec_sum(s.slice(0, 1)) == s@[0]);
    } else {
        // apply induction for i-1 on the same sequence
        spec_sum_prefix_step(s, i - 1);
        // Now reason about slices:
        // s.slice(0, i+1) == s.slice(0, i) + seq![ s@[i] ]
        // Using fold-left properties, the total sum extends by s@[i]
        // We assert these equalities to help the verifier
        assert(spec_sum(s.slice(0, i + 1)) == spec_sum(s.slice(0, i)) + s@[i]);
    }
}
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
fn will_it_fly(qs: &Vec<u32>, w: u32) -> (ret: bool)
    // post-conditions-start
    ensures
        ret <==> qs@ =~= qs@.reverse() && spec_sum(qs@) <= w,
    // post-conditions-end
// </vc-spec>
// <vc-code>
// <vc-code>
{
    // impl-start
    let n: nat = qs.len();
    let mut i: nat = 0;
    let mut pal: bool = true;
    let mut sum: int = 0;
    while i < n
        invariant i <= n
        invariant sum == spec_sum(qs@.slice(0, i))
        invariant pal == (forall |j: nat| j < i ==> #[trigger] qs@[j] == qs@[n - 1 - j])
    {
        // read element
        let x: u32 = qs[i];
        // update sum
        sum = sum + (x as int);
        // update palindrome flag
        if !(qs[i] == qs[n - 1 - i]) {
            pal = false;
        }
        // advance
        i = i + 1;
        // maintain the relationship between prefix sums
        if i <= n {
            // after increment, i was old_i+1, so we can apply lemma for the previous index
            // previous index = i - 1
            if i > 0 && i - 1 < n {
                spec_sum_prefix_step(qs@, i - 1);
            }
        }
    }
    let ret: bool = pal && sum <= (w as int);
    ret
    // impl-end
}
// </vc-code>
// </vc-code>

fn main() {}
}