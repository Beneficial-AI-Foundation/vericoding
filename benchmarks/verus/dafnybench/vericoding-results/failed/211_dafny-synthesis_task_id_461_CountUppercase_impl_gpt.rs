use vstd::prelude::*;

verus! {

spec fn is_upper_case(c: char) -> bool {
    65 <= c as int <= 90
}

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn count_uppercase(s: &str) -> (count: usize)
    ensures 
        count >= 0,
        count as int == s@.filter(|c: char| is_upper_case(c)).len(),
// </vc-spec>
// <vc-code>
{
    let mut count: usize = 0;
    for ch in s.chars() {
        if 65 <= ch as int && ch as int <= 90 {
            count += 1;
        }
    }
    count
}
// </vc-code>

fn main() {}

}