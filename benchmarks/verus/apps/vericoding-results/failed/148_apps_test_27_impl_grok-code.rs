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
fn ranges_equal(s: &[char], start1: usize, start2: usize, len: usize) -> (result: bool)
    requires
        start1 as int + len as int <= s.len() as int,
        start2 as int + len as int <= s.len() as int,
        s.len() <= usize::MAX as nat,
    ensures
        result == s@.subrange(start1 as int, len as int) == s@.subrange(start2 as int, len as int)
{
    if start1 + len > s.len() || start2 + len > s.len() {
        return false;
    }
    let mut i: usize = 0;
    while i < len
        invariant
            s@.subrange(start1 as int, i as int) == s@.subrange(start2 as int, i as int),
    {
        if s[start1 + i] != s[start2 + i] {
            return false;
        }
        i += 1;
    }
    true
}

/* helper modified by LLM (iteration 5): Fix subrange comparison syntax for sequences */
fn max_copy_savings_up_to_exec(s: Vec<char>, n: u8, limit: u8) -> (result: u8)
    requires
        s.len() == n as usize
    ensures
        result as usize == max_copy_savings_up_to(s@, n as nat, limit as nat)
    decreases limit
{
    if limit == 0 {
        0
    } else {
        let i = limit - 1;
        let prefix_len = i as usize + 1;
        let end_pos = i as usize + 1 + prefix_len;
        let current = if end_pos <= n as usize &&
                         ranges_equal(&s, 0, end_pos - prefix_len, prefix_len) {
                         i
                     } else {
                         0
                     };
        let prev = max_copy_savings_up_to_exec(s, n, i);
        if current > prev {
            current
        } else {
            prev
        }
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
{
    /* code modified by LLM (iteration 5): Compute result as n minus max copy savings using exec helper */
    let x = max_copy_savings_up_to_exec(s, n, n / 2);
    let result = n - x;
    result
}
// </vc-code>


}

fn main() {}