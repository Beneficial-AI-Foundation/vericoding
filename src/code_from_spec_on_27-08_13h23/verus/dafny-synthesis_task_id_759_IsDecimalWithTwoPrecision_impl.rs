use vstd::prelude::*;

verus! {

// <vc-helpers>
fn find_decimal_point(s: &str) -> (idx: Option<int>)
    ensures
        match idx {
            Some(i) => 0 <= i < s@.len() && s@[i] == '.',
            None => forall|i: int| 0 <= i < s@.len() ==> s@[i] != '.',
        }
{
    let mut i = 0;
    while i < s@.len()
        invariant
            0 <= i <= s@.len(),
            forall|k: int| 0 <= k < i ==> s@[k] != '.',
    {
        if s@[i] == '.' {
            return Some(i);
        }
        i = i + 1;
    }
    None
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
fn is_decimal_with_two_precision(s: &str) -> (result: bool)
    ensures
        result ==> exists|i: int| 0 <= i < s@.len() && s@[i] == '.' && s@.len() - i - 1 == 2,
        !result ==> !exists|i: int| 0 <= i < s@.len() && s@[i] == '.' && s@.len() - i - 1 == 2,
// </vc-spec>
// </vc-spec>

// <vc-code>
fn is_decimal_with_two_precision(s: &str) -> (result: bool)
    ensures
        result ==> exists|i: int| 0 <= i < s@.len() && s@[i] == '.' && s@.len() - i - 1 == 2,
        !result ==> !exists|i: int| 0 <= i < s@.len() && s@[i] == '.' && s@.len() - i - 1 == 2,
{
    let idx = find_decimal_point(s);
    match idx {
        Some(i) => {
            if s@.len() - i - 1 == 2 {
                true
            } else {
                false
            }
        },
        None => {
            false
        },
    }
}
// </vc-code>

fn main() {
}

}