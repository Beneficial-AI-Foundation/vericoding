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
    let n: nat = qs.len();
    let mut i: nat = 0;
    let mut pal: bool = true;
    let mut sum: int = 0;
    while i < n
        invariant i <= n;
        invariant sum == spec_sum(qs@.slice(0, i));
        invariant pal == (forall |j: nat| j < i ==> #[trigger] qs@[j] == qs@[n - 1 - j]);
        decreases n - i;
    {
        let x: u32 = qs[i];
        let old_sum: int = sum;
        // update palindrome flag based on current index
        if !(qs[i] == qs[n - 1 - i]) {
            pal = false;
        }
        // use lemma about prefix sums at current i
        proof {
            spec_sum_prefix_step(qs@, i);
            // from the loop invariant we know old_sum == spec_sum(qs@.slice(0, i))
            assert(old_sum == spec_sum(qs@.slice(0, i)));
            // lemma gives spec_sum(slice(0,i+1)) == spec_sum(slice(0,i)) + qs@[i]
            assert(spec_sum(qs@.slice(0, i + 1)) == spec_sum(qs@.slice(0, i)) + qs@[i]);
        }
        // update sum and index
        sum = old_sum + (x as int);
        i = i + 1;
        // re-establish sum invariant
        proof {
            assert(sum == spec_sum(qs@.slice(0, i)));
        }
    }
    // after loop, i == n by loop guard
    proof {
        assert(i == n);
        // sum equals total spec sum
        assert(sum == spec_sum(qs@.slice(0, n)));
        assert(sum == spec_sum(qs@));
        // pal corresponds to full-sequence palindrome property
        assert(pal == (forall |j: nat| j < n ==> #[trigger] qs@[j] == qs@[n - 1 - j]));
        // relate the forall characterization to sequence reverse equality
        assert(qs@.len() == n);
        assert((forall |j: nat| j < n ==> #[trigger] qs@[j] == qs@[n - 1 - j]) == (qs@ =~= qs@.reverse()));
    }
    let ret: bool = pal && sum <= (w as int);
    proof {
        // relate ret to the specification's predicate
        assert(ret == (qs@ =~= qs@.reverse() && spec_sum(qs@) <= (w as int)));
    }
    ret
}
// </vc-code>
// </vc-code>

fn main() {}
}