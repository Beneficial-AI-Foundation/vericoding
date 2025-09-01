use vstd::prelude::*;

verus! {

// <vc-helpers>
proof fn lemma_reverse_index<A>(s: Seq<A>, i: int)
    requires
        0 <= i < s.len(),
    ensures
        s.index(i) == s.index(s.len() - 1 - i),
{
}

spec fn is_palindrome_spec(text: Seq<char>) -> bool {
    forall|i: int| 0 <= i < text.len() ==> text.index(i) == text.index(text.len() - 1 - i)
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
            result == forall|j: int| 0 <= j < left || right < j < n ==> text@.index(j) == text@.index(n - 1 - j),
            result ==> forall|j: int| 0 <= j < left ==> text@.index(j) == text@.index(n - 1 - j),
    {
        let left_i: int = left as int;
        let right_i: int = right as int;
        
        if text@.index(left_i) != text@.index(right_i) {
            result = false;
            break;
        }
        
        proof {
            lemma_reverse_index(text@, left_i);
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