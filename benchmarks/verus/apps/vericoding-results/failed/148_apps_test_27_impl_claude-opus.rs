// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(n: nat, s: Seq<char>) -> bool {
    s.len() == n
}

spec fn max_copy_savings(s: Seq<char>, n: nat) -> nat {
    max_copy_savings_up_to(s, n, n / 2)
}

spec fn max_copy_savings_up_to(s: Seq<char>, n: nat, limit: nat) -> nat
    decreases limit
{
    if limit == 0 { 0 }
    else {
        let i = (limit - 1) as nat;
        let current = if can_copy_at(s, n, i) { i } else { 0 };
        let prev = max_copy_savings_up_to(s, n, i);
        if current > prev { current } else { prev }
    }
}

spec fn can_copy_at(s: Seq<char>, n: nat, i: nat) -> bool {
    let prefix_len = i + 1;
    let end_pos = i + 1 + prefix_len;
    end_pos <= n && s.subrange(0, prefix_len as int) == s.subrange((i+1) as int, end_pos as int)
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn solve(n: u8, s: Vec<char>) -> (result: u8)
    requires 
        valid_input(n as nat, s@)
    ensures 
        result as nat <= n as nat,
        n == 0 ==> result == 0,
        n > 0 ==> result >= 1,
        result as nat == n as nat - max_copy_savings(s@, n as nat)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed syntax error in inner while loop invariant */
    if n == 0 {
        return 0;
    }
    
    let mut max_savings: u8 = 0;
    let mut i: u8 = 0;
    
    while i < n / 2
        invariant
            i <= n / 2,
            max_savings <= i,
            max_savings as nat == max_copy_savings_up_to(s@, n as nat, i as nat),
            max_savings <= n / 2,
        decreases n / 2 - i
    {
        let prefix_len = i + 1;
        let end_pos = i + 1 + prefix_len;
        
        if end_pos <= n {
            let mut matches = true;
            let mut j: u8 = 0;
            
            while j < prefix_len
                invariant
                    j <= prefix_len,
                    prefix_len == i + 1,
                    end_pos == i + 1 + prefix_len,
                    end_pos <= n,
                    j as usize <= s.len(),
                    (i + 1 + j) as usize <= s.len(),
                    matches == (j == 0 || s@.subrange(0, j as int) == s@.subrange((i + 1) as int, (i + 1 + j) as int)),
                decreases prefix_len - j
            {
                if j as usize < s.len() && (i + 1 + j) as usize < s.len() {
                    if s[j as usize] != s[(i + 1 + j) as usize] {
                        matches = false;
                    }
                }
                j = j + 1;
            }
            
            if matches {
                if prefix_len > max_savings {
                    max_savings = prefix_len;
                }
            }
        }
        
        i = i + 1;
    }
    
    n - max_savings
}
// </vc-code>


}

fn main() {}