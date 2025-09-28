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
/* helper modified by LLM (iteration 5): Fixed compilation error by changing `spec fn` to `fn` for `base26_to_string_appended` and moving it out of the code section. */
fn base26_to_string_appended(val: nat, k_suffix: int) -> Seq<char>
    decreases k_suffix when k_suffix >= 0
{
    if k_suffix == 0 { Seq::empty() }
    else { base26_to_string_appended(val / 26, k_suffix - 1).add(seq![((val % 26) + ('a' as int)) as char]) }
}

fn convert_to_base26(s_input: &Vec<char>) -> (result: nat)
    requires
        forall|i: int| 0 <= i < s_input.len() ==> 'a' <= #[trigger] s_input[i] <= 'z',
    ensures
        result == string_to_base26(s_input@),
{
    let mut result: nat = 0;
    let mut mult: nat = 1;
    let mut i: int = (s_input.len() as int) - 1;
    while i >= 0
        invariant
            0 <= i + 1,
            (i as nat) + 1 <= s_input.len(),
            mult == pow26((s_input.len() as nat) - (i as nat) - 1),
            result == (string_to_base26(s_input.subrange((i as int) + 1, s_input.len() as int))),
            forall|j: int| (i as int) + 1 <= j < s_input.len() ==> 'a' <= s_input[j] <= 'z',
        decreases i
    {
        let val: nat = ((s_input[i as usize] as int) - ('a' as int)) as nat;
        result = result + val * mult;

        proof {
            assert(mult == pow26((s_input.len() as nat) - (i as nat) - 1));
            assert(mult * 26 == pow26((s_input.len() as nat) - (i as nat)));
        }

        mult = mult * 26;
        i = i - 1;
    }
    result
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
/* code modified by LLM (iteration 5): Removed redundant loop and variable, simplified direct computation of character values based on the spec. */
{
    let s_val = convert_to_base26(&s);
    let t_val = convert_to_base26(&t);
    let initial_sum_val = s_val + t_val;
    let median_val = initial_sum_val / 2;

    let mut result_vec: Vec<char> = Vec::new();
    let mut i: int = 0;

    while i < k as int
        invariant
            i >= 0,
            i <= k as int,
            result_vec.len() == i,
            forall|idx: int| 0 <= idx < i ==> 'a' <= #[trigger] result_vec[idx] <= 'z',
            result_vec@ == base26_to_string(median_val, i)
        decreases (k as int) - i
    {
        // We need to calculate the character at the current position 'i'
        // from the `median_val`. The `base26_to_string` function builds the string
        // from the least significant digit upwards, so the digit for the current position 'i'
        // is `(median_val / pow26((k as nat) - 1 - (i as nat))) % 26`
        let char_val_num: nat = (median_val / pow26((k as nat) - 1 - (i as nat))) % 26;
        result_vec.push(((char_val_num + 'a' as int) as char));
        i = i + 1;
    }

    proof {
        assert(result_vec@ == median_string(s@, t@, k as int));
    }
    result_vec
}
// </vc-code>


}

fn main() {}