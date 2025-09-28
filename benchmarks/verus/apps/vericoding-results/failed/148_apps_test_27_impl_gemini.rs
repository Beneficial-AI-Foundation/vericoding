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
/* helper modified by LLM (iteration 5): [removed overly-restrictive requires clause that caused a compilation error] */
fn can_copy_at_impl(s: &Vec<char>, n: u8, i: u8) -> (res: bool)
    requires
        valid_input(n as nat, s@),
    ensures
        res == can_copy_at(s@, n as nat, i as nat),
{
    let prefix_len = (i as usize) + 1;
    let start_of_next_part = (i as usize) + 1;
    let end_pos = start_of_next_part + prefix_len;

    if end_pos > (n as usize) {
        return false;
    }
    
    s.as_slice()[0..prefix_len] == s.as_slice()[start_of_next_part..end_pos]
}

fn find_max_savings_index(n: u8, s: &Vec<char>) -> (max_i: u8)
    requires
        valid_input(n as nat, s@),
    ensures
        max_i as nat == max_copy_savings(s@, n as nat),
{
    let mut current_max: u8 = 0;
    let mut k: u8 = 0;
    let limit = n / 2;
    while k < limit
        invariant
            k <= limit,
            valid_input(n as nat, s@),
            current_max as nat == max_copy_savings_up_to(s@, n as nat, k as nat),
        decreases limit - k
    {
        let can_copy = can_copy_at_impl(s, n, k);
        let prev = current_max;
        let current = if can_copy { k } else { 0 };
        
        if current > prev {
            current_max = current;
        }
        
        k = k + 1;
    }
    current_max
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
/* code modified by LLM (iteration 5): [no changes needed, kept correct logic from previous turn] */
{
    if n == 0 {
        return 0;
    }
    let max_i = find_max_savings_index(n, &s);
    let result = n - max_i;
    result
}
// </vc-code>


}

fn main() {}