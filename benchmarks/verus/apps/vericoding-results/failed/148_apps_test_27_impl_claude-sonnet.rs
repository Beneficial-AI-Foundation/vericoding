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
/* helper modified by LLM (iteration 5): Fixed nat literal syntax error */
fn lemma_max_copy_savings_monotonic(s: Seq<char>, n: nat, limit1: nat, limit2: nat)
    requires
        limit1 <= limit2,
        limit2 <= n / 2
    ensures
        max_copy_savings_up_to(s, n, limit1) <= max_copy_savings_up_to(s, n, limit2)
    decreases limit2
{
    if limit1 == limit2 {
        return;
    }
    if limit2 == 0 {
        return;
    }
    proof {
        let prev_limit = (limit2 - 1) as nat;
        lemma_max_copy_savings_monotonic(s, n, limit1, prev_limit);
    }
}

fn lemma_can_copy_bounds(s: Seq<char>, n: nat, i: nat)
    requires
        can_copy_at(s, n, i)
    ensures
        i < n / 2
{
    proof {
        let prefix_len = (i + 1) as nat;
        let end_pos = (i + 1 + prefix_len) as nat;
        assert(end_pos == 2 * (i + 1));
        assert(end_pos <= n);
        assert(2 * (i + 1) <= n);
        assert(i + 1 <= n / 2);
        assert(i < n / 2);
    }
}
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
/* code modified by LLM (iteration 5): Fixed nat literal syntax error */
{
    if n == 0 {
        return 0;
    }
    
    let mut max_savings: u8 = 0;
    let mut i: u8 = 0;
    let limit = n / 2;
    
    while i < limit
        invariant
            i <= limit,
            limit == n / 2,
            max_savings as nat == max_copy_savings_up_to(s@, n as nat, i as nat),
            max_savings <= i
        decreases limit - i
    {
        proof {
            let prefix_len = (i + 1) as nat;
            let end_pos = (i + 1) as nat + prefix_len;
        }
        
        if (i + 1) + (i + 1) <= n {
            let mut matches = true;
            let mut j: u8 = 0;
            
            while j < (i + 1) && matches
                invariant
                    j <= i + 1,
                    matches ==> (forall|k: int| 0 <= k < j ==> s@[k] == s@[(i + 1 + k) as int]),
                    !matches ==> (exists|k: int| 0 <= k < j && s@[k] != s@[(i + 1 + k) as int])
                decreases (i + 1) - j
            {
                if s[j as usize] != s[(i + 1 + j) as usize] {
                    matches = false;
                }
                j += 1;
            }
            
            if matches {
                proof {
                    assert(can_copy_at(s@, n as nat, i as nat));
                }
                max_savings = i;
            }
        }
        
        proof {
            let current = if can_copy_at(s@, n as nat, i as nat) { i as nat } else { 0 };
            let prev = max_copy_savings_up_to(s@, n as nat, i as nat);
            let next = max_copy_savings_up_to(s@, n as nat, (i + 1) as nat);
            assert(next == if current > prev { current } else { prev });
        }
        
        i += 1;
    }
    
    proof {
        assert(max_savings as nat == max_copy_savings_up_to(s@, n as nat, limit as nat));
        assert(limit as nat == n as nat / 2);
        assert(max_savings as nat == max_copy_savings(s@, n as nat));
    }
    
    n - max_savings
}
// </vc-code>


}

fn main() {}