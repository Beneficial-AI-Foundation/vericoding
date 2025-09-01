use vstd::prelude::*;

verus! {

// pure-end

spec fn spec_sum(s: Seq<u32>) -> (ret:int) {
    s.fold_left(0, |x: int, y| x + y)
}
// pure-end

// <vc-helpers>
fn is_palindrome(s: Seq<u32>) -> (ret: bool)
    ensures
        ret <==> s =~= s.reverse(),
{
    let mut i: int = 0;
    let mut j: int = s.len() - 1;

    #[invariant(
        i >= 0,
        j < s.len(),
        i <= j + 1,
        forall|k: int| 0 <= k < i ==> s[k] == s[s.len() - 1 - k],
        forall|k: int| j < k < s.len() ==> s[k] == s[s.len() - 1 - k],
    )]
    while i < j
    {
        if s[i] != s[j] {
            return false;
        }
        i = i + 1;
        j = j - 1;
    }
    true
}
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
    let qs_seq = qs.view();
    let sum_qs = spec_sum(qs_seq);
    let palindrome = is_palindrome(qs_seq);

    (palindrome && sum_qs <= w as int)
}
// </vc-code>

fn main() {}
}