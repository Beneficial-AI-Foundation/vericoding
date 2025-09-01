use vstd::prelude::*;

verus! {

// pure-end

spec fn spec_sum(s: Seq<u32>) -> (ret:int) {
    s.fold_left(0, |x: int, y| x + y)
}
// pure-end

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn will_it_fly(qs: &Vec<u32>, w: u32) -> (ret: bool)
    // post-conditions-start
    ensures
        ret <==> qs@ =~= qs@.reverse() && spec_sum(qs@) <= w,
    // post-conditions-end
// </vc-spec>
// <vc-code>
fn will_it_fly(qs: &Vec<u32>, w: u32) -> (ret: bool)
    // post-conditions-start
    ensures
        ret <==> qs@ =~= qs@.reverse() && spec_sum(qs@) <= w,
    // post-conditions-end
{
    let s = qs@;
    let mut sum: int = 0;
    let mut i: usize = 0;
    while i < qs.len() {
        sum += qs[i] as int;
        i += 1;
    }
    assert(sum == spec_sum(s));
    if sum > w as int {
        return false;
    }
    // palindrome check
    let len = qs.len();
    i = 0;
    while i < (len / 2)
        invariant
            forall |j: int| 0 <= j < i ==> s[j] == s[len - 1 - j]
    {
        let rev_i = len - 1 - i;
        if qs[i] != qs[rev_i] {
            return false;
        }
        i += 1;
    }
    // assert palindrome
    proof {
        assert(s =~= s.reverse());
    }
    true
}
// </vc-code>

fn main() {}
}