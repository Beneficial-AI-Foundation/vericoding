use vstd::prelude::*;

verus! {

spec fn is_upper_case(c: char) -> (ret:bool) {
    c >= 'A' && c <= 'Z'
}
// pure-end
// pure-end

spec fn count_uppercase_sum(seq: Seq<char>) -> (ret:int)
    decreases seq.len(),
{
    if seq.len() == 0 {
        0
    } else {
        count_uppercase_sum(seq.drop_last()) + if is_upper_case(seq.last()) {
            seq.last() as int
        } else {
            0 as int
        }
    }
}
// pure-end

// <vc-helpers>
// <vc-helpers>
// (No helpers needed)
 // </vc-helpers>
// </vc-helpers>

// <vc-spec>
fn digit_sum(text: &[char]) -> (sum: u128)
    // post-conditions-start
    ensures
        count_uppercase_sum(text@) == sum,
    // post-conditions-end
// </vc-spec>
// <vc-code>
// <vc-code>
{
    // impl-start
    let mut i: nat = 0;
    let mut acc: u128 = 0;
    while i < (text.len() as nat)
        invariant { i <= (text.len() as nat) && #[trigger] count_uppercase_sum(text@.slice(0, i)) == (acc as int); }
    {
        let c: char = text[i as usize];
        let old_acc = acc;
        if is_upper_case(c) {
            acc = acc + ((c as u32) as u128);
            proof {
                assert((acc as int) == (old_acc as int) + (c as int));
            }
        } else {
            proof {
                assert((acc as int) == (old_acc as int));
            }
        }

        proof {
            let s = text@.slice(0, i + 1);
            assert(s.drop_last() == text@.slice(0, i));
            assert(s.last() == text@[i]);
            assert(count_uppercase_sum(s) == count_uppercase_sum(s.drop_last()) + if is_upper_case(s.last()) { s.last() as int } else { 0 as int });
            assert(count_uppercase_sum(s) == count_uppercase_sum(text@.slice(0, i)) + if is_upper_case(c) { c as int } else { 0 as int });
            assert((old_acc as int) == count_uppercase_sum(text@.slice(0, i)));
            assert((acc as int) == count_uppercase_sum(text@.slice(0, i + 1)));
        }

        i = i + 1;
    }
    assert((acc as int) == count_uppercase_sum(text@));
    acc
    // impl-end
}
// </vc-code>
// </vc-code>

} // verus!
fn main() {}