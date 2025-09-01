use vstd::prelude::*;

verus! {

// pure-end

spec fn spec_sum(s: Seq<u32>) -> (ret:int) {
    s.fold_left(0, |x: int, y| x + y)
}
// pure-end

// <vc-helpers>
spec fn is_palindrome (s: Seq<u32>) -> bool {
    forall |i: int| #[trigger] (0 <= i < s.len()) ==> s[i] == s[s.len() - 1 - i]
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
    let len = qs.len();
    let mut i = 0;
    let mut sum: i64 = 0;
    let mut is_pali = true;
    while i < len / 2 
        invariant
            0 <= i <= len / 2,
            sum as int == spec_sum(qs@.take(i as int)) + spec_sum(qs@.drop(len - i as int)),
            is_pali == forall |j: int| 0 <= j < i ==> qs@[j] == qs@[len - 1 - j],
    {
        if qs@[i] != qs@[len - 1 - i] {
            is_pali = false;
        }
        sum = sum + ((qs@[i]) as i64) + ((qs@[len - 1 - i]) as i64);
        i = i + 1;
    }
    if len % 2 == 1 {
        sum = sum + (qs@[len / 2] as i64);
    }
    proof {
        assert( is_pali == (forall |j: int| 0 <= j < len / 2 ==> qs@[j] == qs@[len - 1 - j]) );
        if is_pali {
            assert( is_palindrome(qs@) );
        }
        assert( sum as int == spec_sum(qs@) );
    }
    is_pali && (sum as int <= w as int)
}
// </vc-code>

fn main() {}
}