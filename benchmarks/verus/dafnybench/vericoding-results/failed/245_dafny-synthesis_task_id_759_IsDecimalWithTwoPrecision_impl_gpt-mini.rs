use vstd::prelude::*;

verus! {

// <vc-helpers>
// no helpers needed
// </vc-helpers>

// <vc-spec>
fn is_decimal_with_two_precision(s: &str) -> (result: bool)
    ensures
        result ==> exists|i: int| 0 <= i < s@.len() && s@[i] == '.' && s@.len() - i - 1 == 2,
        !result ==> !exists|i: int| 0 <= i < s@.len() && s@[i] == '.' && s@.len() - i - 1 == 2,
// </vc-spec>
// <vc-code>
{
    let char_count: usize = s.chars().count();
    let mut found_index: Option<usize> = None;
    let mut idx: usize = 0;
    for c in s.chars() {
        if c == '.' {
            if char_count - idx - 1 == 2 {
                found_index = Some(idx);
                break;
            }
        }
        idx += 1;
    }
    let res: bool = match found_index { Some(_) => true, None => false };
    proof {
        let seq: Seq<char> = s@;
        match found_index {
            Some(j) => {
                let k: int = j as int;
                assert(0 <= k && k < seq.len() as int);
                assert(seq@[k as nat] == '.');
                assert(seq.len() as int - k - 1 == 2);
                assert(exists |i: int| 0 <= i && i < seq.len() as int && seq@[i as nat] == '.' && seq.len() as int - i - 1 == 2);
            }
            None => {
                assert(!exists |i: int| 0 <= i && i < seq.len() as int && seq@[i as nat] == '.' && seq.len() as int - i - 1 == 2);
            }
        }
    }
    return res;
}
// </vc-code>

fn main() {
}

}