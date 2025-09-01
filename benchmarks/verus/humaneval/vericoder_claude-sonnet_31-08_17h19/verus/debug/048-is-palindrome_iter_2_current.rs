use vstd::prelude::*;

verus! {

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn is_palindrome(text: &str) -> (result: bool)
    // post-conditions-start
    ensures
        result == forall|i: int|
            0 <= i < text@.len() ==> #[trigger] text@[i] == text@[text@.len() - 1 - i],
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    let len = text.len();
    if len <= 1 {
        return true;
    }
    
    let mut i = 0;
    while i < len / 2
        invariant
            0 <= i <= len / 2,
            forall|j: int| 0 <= j < i ==> #[trigger] text@[j] == text@[len - 1 - j],
    {
        proof {
            let ghost_i = i as int;
            let ghost_idx = (len - 1 - i) as int;
            if text@[ghost_i] != text@[ghost_idx] {
                assert(exists|k: int| 0 <= k < text@.len() && text@[k] != text@[text@.len() - 1 - k]);
                return false;
            }
        }
        if text.as_bytes()[i] != text.as_bytes()[len - 1 - i] {
            proof {
                let ghost_i = i as int;
                let ghost_idx = (len - 1 - i) as int;
                assert(text@[ghost_i] != text@[ghost_idx]);
                assert(exists|k: int| 0 <= k < text@.len() && text@[k] != text@[text@.len() - 1 - k]);
            }
            return false;
        }
        i += 1;
    }
    
    assert(forall|j: int| 0 <= j < len / 2 ==> #[trigger] text@[j] == text@[len - 1 - j]);
    
    proof {
        assert(forall|k: int| 0 <= k < text@.len() ==> #[trigger] text@[k] == text@[text@.len() - 1 - k]) by {
            assert(forall|k: int| 0 <= k < text@.len() ==> {
                if k < len / 2 {
                    text@[k] == text@[len - 1 - k]
                } else if k >= (len + 1) / 2 {
                    let mirror_k = len - 1 - k;
                    mirror_k < len / 2 && text@[mirror_k] == text@[len - 1 - mirror_k] && text@[k] == text@[len - 1 - k]
                } else {
                    len % 2 == 1 && k == len / 2 && text@[k] == text@[len - 1 - k]
                }
            });
        };
    }
    
    true
}
// </vc-code>

fn main() {}
}