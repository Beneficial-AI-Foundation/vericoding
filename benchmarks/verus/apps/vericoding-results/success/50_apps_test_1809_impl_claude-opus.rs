// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_valid_input(s: Seq<char>) -> bool {
    s.len() >= 5 && s[s.len() as int - 1] == '\n'
}

spec fn calculate_result_from_input(s: Seq<char>) -> Seq<char> {
    s /* placeholder implementation */
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn solve(s: Vec<char>) -> (result: Vec<char>)
    requires 
        s.len() > 0,
        (exists|i: int| 0 <= i < s.len() as int && s@[i] == '\n'),
        is_valid_input(s@),
    ensures 
        result.len() > 0,
        result@[result.len() as int - 1] == '\n'
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): added decreases clause to while loop */
    let mut result = Vec::new();
    let n = s.len();
    
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            n == s.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result@[j] == s@[j],
        decreases n - i
    {
        result.push(s[i]);
        i = i + 1;
    }
    
    assert(result.len() > 0) by {
        assert(n > 0);
        assert(i == n);
        assert(result.len() == n);
    }
    
    assert(result@[result.len() as int - 1] == '\n') by {
        assert(s@[s.len() as int - 1] == '\n');
        assert(result.len() == s.len());
        assert(result@[result.len() as int - 1] == s@[s.len() as int - 1]);
    }
    
    result
}
// </vc-code>


}

fn main() {}