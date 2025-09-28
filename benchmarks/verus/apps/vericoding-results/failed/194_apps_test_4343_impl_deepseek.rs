// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn median_string(s: Seq<char>, t: Seq<char>, k: int) -> Seq<char> {
    let s_val = string_to_base26(s);
    let t_val = string_to_base26(t);
    let median_val = (s_val + t_val) / 2;
    base26_to_string(median_val, k)
}

spec fn string_to_base26(s: Seq<char>) -> nat
    decreases s.len()
{
    if s.len() == 0 { 0 }
    else { ((s[0] as int - 'a' as int) * pow26((s.len() - 1) as nat) + string_to_base26(s.subrange(1, s.len() as int))) as nat }
}

spec fn base26_to_string(val: nat, k: int) -> Seq<char>
    decreases k when k >= 1
{
    if k == 1 { seq![((val % 26) + ('a' as int)) as char] }
    else { base26_to_string(val / 26, k - 1).add(seq![((val % 26) + ('a' as int)) as char]) }
}

spec fn pow26(n: nat) -> nat
    decreases n
{
    if n == 0 { 1 } else { 26 * pow26((n - 1) as nat) }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): add missing pow26_positive helper function */
proof fn pow26_positive(n: nat)
    ensures
        pow26(n) > 0,
    decreases n
{
    if n > 0 {
        pow26_positive((n - 1) as nat);
    }
}

/* helper modified by LLM (iteration 4): fix type casting for execution context */
proof fn string_to_base26_bounds(s: Seq<char>, k: int)
    requires
        s.len() == k,
        k >= 0,
        forall|i: int| 0 <= i < k ==> 'a' <= s[i] <= 'z',
    ensures
        string_to_base26(s) < pow26(k),
    decreases k
{
    if k > 0 {
        assert(0 <= s[0] as int - 'a' as int <= 25);
        string_to_base26_bounds(s.subrange(1, s.len() as int), k - 1);
        pow26_positive((k - 1) as nat);
    }
}

proof fn base26_to_string_length(val: nat, k: int)
    requires
        k >= 1,
        val < pow26(k),
    ensures
        base26_to_string(val, k).len() == k,
    decreases k
{
    if k > 1 {
        base26_to_string_length(val / 26, k - 1);
    }
}

proof fn base26_to_string_bounds(val: nat, k: int)
    requires
        k >= 1,
        val < pow26(k),
    ensures
        forall|i: int| 0 <= i < k ==> 'a' <= base26_to_string(val, k)[i] <= 'z',
    decreases k
{
    if k > 1 {
        base26_to_string_bounds(val / 26, k - 1);
        assert(val % 26 < 26);
    }
}

proof fn median_bounds(s_val: nat, t_val: nat, k: int)
    requires
        s_val < pow26(k),
        t_val < pow26(k),
    ensures
        (s_val + t_val) / 2 < pow26(k),
{
    assert((s_val + t_val) / 2 <= s_val + t_val < 2 * pow26(k));
    assert((s_val + t_val) / 2 < pow26(k));
}
// </vc-helpers>

// <vc-spec>
fn solve(k: usize, s: Vec<char>, t: Vec<char>) -> (result: Vec<char>)
    requires 
        k >= 1,
        s.len() == k,
        t.len() == k,
        forall|i: int| 0 <= i < k ==> 'a' <= #[trigger] s[i] <= 'z',
        forall|i: int| 0 <= i < k ==> 'a' <= #[trigger] t[i] <= 'z',
    ensures 
        result.len() == k,
        forall|i: int| 0 <= i < k ==> 'a' <= #[trigger] result[i] <= 'z',
        result@ == median_string(s@, t@, k as int),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fix int casting in execution context */
    let s_val_nat = string_to_base26(s@);
    let t_val_nat = string_to_base26(t@);
    proof {
        string_to_base26_bounds(s@, k);
        string_to_base26_bounds(t@, k);
        median_bounds(s_val_nat, t_val_nat, k);
        base26_to_string_bounds((s_val_nat + t_val_nat) / 2, k);
        base26_to_string_length((s_val_nat + t_val_nat) / 2, k);
    }
    
    let median_val = (s_val_nat + t_val_nat) / 2;
    let result_seq = base26_to_string(median_val, k);
    
    let mut result: Vec<char> = Vec::with_capacity(k);
    let mut i: usize = 0;
    
    while i < k
        invariant
            i <= k,
            result.len() == i,
            forall|j: int| 0 <= j < i ==> 'a' <= #[trigger] result[j] <= 'z',
            result@ == result_seq.subrange(0, i),
    {
        result.push(result_seq[i]);
        i += 1;
    }
    
    result
}
// </vc-code>


}

fn main() {}