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

proof fn lemma_max_copy_savings_up_to_monotonic(s: Seq<char>, n: nat, limit1: nat, limit2: nat)
    requires
        limit1 <= limit2,
    ensures
        max_copy_savings_up_to(s, n, limit1) <= max_copy_savings_up_to(s, n, limit2)
    decreases limit2
{
    if limit2 == 0 {
        assert(limit1 == 0);
    } else if limit1 < limit2 {
        lemma_max_copy_savings_up_to_monotonic(s, n, limit1, (limit2 - 1) as nat);
    }
    let i = (limit2 - 1) as nat;
    let current = if can_copy_at(s, n, i) { i } else { 0 };
    let prev = max_copy_savings_up_to(s, n, (limit2 - 1) as nat);
    assert(max_copy_savings_up_to(s, n, limit2) >= prev);
}

proof fn lemma_max_copy_savings_bounds(s: Seq<char>, n: nat)
    ensures
        max_copy_savings(s, n) <= n / 2
{
    lemma_max_copy_savings_up_to_monotonic(s, n, 0, n / 2);
}

/* helper modified by LLM (iteration 5): Fix quantifier trigger annotation */
fn find_max_copy_savings(s: &Vec<char>, n: u8) -> (savings: u8)
    requires
        n as nat == s@.len(),
    ensures
        savings as nat == max_copy_savings_up_to(s@, n as nat, (n / 2) as nat),
        savings <= n / 2
{
    let mut max_savings = 0;
    let mut i: u8 = 0;
    let limit = n / 2;
    
    while i < limit
        invariant
            i <= limit,
            max_savings as nat == max_copy_savings_up_to(s@, n as nat, i as nat),
            max_savings <= n / 2,
        decreases (limit - i) as int
    {
        let prefix_len = i + 1;
        let end_pos = i + 1 + prefix_len;
        
        if end_pos <= n {
            let mut can_copy = true;
            let mut j: u8 = 0;
            
            while j <= i
                invariant
                    j <= i + 1,
                    can_copy == (forall |k: nat| #[trigger] k < j as nat ==> s@[k as int] == s@[(i + 1 + k) as int]),
                decreases (i - j) as int
            {
                if j <= i {
                    if s[j as usize] != s[(i + 1 + j) as usize] {
                        can_copy = false;
                    }
                    j = j + 1;
                }
            }
            
            if can_copy {
                if i > max_savings {
                    max_savings = i;
                }
            }
        }
        
        i = i + 1;
    }
    
    max_savings
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
{
    /* code modified by LLM (iteration 5): Fix trigger annotation and keep main logic */
    if n == 0 {
        return 0;
    }
    
    let savings = find_max_copy_savings(&s, n);
    let result = n - savings;
    result
}
// </vc-code>


}

fn main() {}