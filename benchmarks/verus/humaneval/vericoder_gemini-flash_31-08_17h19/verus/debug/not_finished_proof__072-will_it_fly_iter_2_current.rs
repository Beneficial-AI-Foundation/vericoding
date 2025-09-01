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
        // The previously verified range was off for the palindrome check. 
        // This ensures the portion of the sequence from index 0 up to `i` (exclusive)
        // matches the section from `s.len() - i` to `s.len()` (exclusive),
        // correctly reflecting the 'scanned' part of the palindrome.
        forall|k: int| 0 <= k < i ==> s[k] == s[s.len() - 1 - k],
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

    // The sum_qs is int, and w is u32, so cast w to int.
    // The previous error was that using 'as int' on `w` (a u32) on the right side of comparison was getting evaluated
    // in concrete code unnecessarily. It's only needed for ghost code verification.
    // Making `w_int` a ghost variable makes the comparison happen in ghost context.
    let ghost w_int = w as int;
    (palindrome && sum_qs <= w_int)
}
// </vc-code>

fn main() {}
}