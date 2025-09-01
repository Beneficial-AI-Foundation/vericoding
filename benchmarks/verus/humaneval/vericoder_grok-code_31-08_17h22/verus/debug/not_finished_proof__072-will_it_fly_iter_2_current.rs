use vstd::prelude::*;

verus! {

// pure-end

spec fn spec_sum(s: Seq<u32>) -> (ret:int) {
    s.fold_left(0, |x: int, y| x + y)
}
// pure-end

// <vc-helpers>
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
{
    let s = qs@;
    let mut sum: int = 0;
    let mut i: usize = 0;
    while i < qs.len()
        invariant
            i <= qs.len(),
            sum == spec_sum(qs@.take(i as int))
    {
        sum += qs[i] as int;
        i += 1;
    }
    assert(sum == spec_sum(s));
    if sum > w as int {
        return false;
    }
    // palindrome check
    let len = s.len() as usize;
    i = 0;
    while i < (len / 2)
        invariant
            forall |j: int| 0 <= j < i ==> s[j] == s[(len - 1) - (j as usize) as int]
    {
        let rev_i = (len - 1) - i;
        if qs[i] != qs[rev_i] {
            return false;
        }
        i += 1;
    }
    // assert palindrome
    proof {
        assert(s.len() % 2 == 0 || s[(s.len() / 2)] == s[(s.len() / 2)]);
        assert forall |j: int| 0 <= j < s.len() implies s[j] == s[s.len() - 1 - j] by {
            if j < s.len() / 2 {
                // assert from loop invariant
            } else if j == s.len() - 1 - (s.len() / 2) {
                // symmetric
            } else if j == s.len() / 2 && s.len() % 2 == 1 {
                // middle
            } else {
                // symmetric
            }
        }
        assert(s =~= s.reverse());
    }
    true
}
// </vc-code>

fn main() {}
}