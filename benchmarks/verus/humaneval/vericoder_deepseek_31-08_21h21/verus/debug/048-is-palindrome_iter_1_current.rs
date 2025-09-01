use vstd::prelude::*;

verus! {

// <vc-helpers>
proof fn lemma_reverse_index<A>(s: Seq<A>, i: int)
    requires
        0 <= i < s.len(),
    ensures
        s[i] == s[s.len() - 1 - i],
{
}

spec fn is_palindrome_spec(text: Seq<char>) -> bool {
    forall|i: int| 0 <= i < text.len() ==> text[i] == text[text.len() - 1 - i]
}
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
    let n = text.len();
    let mut left: usize = 0;
    let mut right: usize = n;
    if n > 0 {
        right = n - 1;
    }
    
    let mut result = true;
    
    while left < right
        invariant
            left <= right,
            left <= n,
            right <= n,
            result == forall|j: int| 0 <= j < left || right < j < n ==> text@[j] == text@[n - 1 - j],
            result ==> forall|j: int| 0 <= j < left ==> text@[j] == text@[n - 1 - j],
    {
        if text@[left] != text@[right] {
            result = false;
            break;
        }
        
        proof {
            lemma_reverse_index(text@, left as int);
        }
        
        left = left + 1;
        if right > 0 {
            right = right - 1;
        }
    }
    
    assert(result == is_palindrome_spec(text@));
    result
}
// </vc-code>

fn main() {}
}