// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fix compilation error by removing as int conversion */
proof fn index_access(s: Seq<char>, i: int)
    requires
        0 <= i < s.len(),
    ensures
        s[i] == s@[i as nat],
{
}

proof fn palindrome_recursive(s: Seq<char>, left: int, right: int)
    requires
        0 <= left <= right < s.len(),
    ensures
        (forall|i: int| left <= i <= right ==> s[i] == s[s.len() - 1 - i]) <==> 
        (s[left] == s[s.len() - 1 - left] && (left + 1 > right - 1 || (forall|i: int| left + 1 <= i <= right - 1 ==> s[i] == s[s.len() - 1 - i]))),
{
    if left < right {
        palindrome_recursive(s, left + 1, right - 1);
    }
}

proof fn nat_to_int_conversion(n: nat) 
    ensures 
        (n as int) >= 0,
{
}
// </vc-helpers>

// <vc-spec>
fn is_palindrome(x: Seq<char>) -> (result: bool)
    ensures
        result <==> (forall|i: int| 0 <= i < x.len() ==> #[trigger] x[i] == x[x.len() - 1 - i]),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Fix compilation error by removing as int conversion */
{
    let mut left: int = 0;
    let mut right: int = x.len() - 1;
    
    while left < right
        invariant
            0 <= left <= right < x.len(),
            forall|i: int| 0 <= i < left || right < i < x.len() ==> x[i] == x[x.len() - 1 - i],
    {
        proof {
            index_access(x, left);
            index_access(x, x.len() - 1 - left);
            index_access(x, right);
            index_access(x, x.len() - 1 - right);
        }
        
        if x[left] != x[x.len() - 1 - left] {
            return false;
        }
        if x[right] != x[x.len() - 1 - right] {
            return false;
        }
        
        proof {
            palindrome_recursive(x, left, right);
        }
        
        left = left + 1;
        right = right - 1;
    }
    
    true
}
// </vc-code>

}
fn main() {}