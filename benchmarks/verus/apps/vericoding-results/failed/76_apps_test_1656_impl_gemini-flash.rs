// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn wow_factor(s: Seq<char>) -> int {
    if s.len() < 4 { 0 }
    else {
        wow_factor_sum(s, 0)
    }
}

spec fn count_vv_pairs_before(s: Seq<char>, pos: int) -> int
    decreases pos
{
    if pos <= 1 { 0 }
    else {
        let prev = count_vv_pairs_before(s, pos - 1);
        if s[pos-1] == 'v' && s[pos-2] == 'v' { prev + 1 } else { prev }
    }
}

spec fn count_vv_pairs_after(s: Seq<char>, pos: int) -> int
    decreases s.len() - pos
{
    if pos >= s.len() - 1 { 0 }
    else {
        let rest = count_vv_pairs_after(s, pos + 1);
        if pos + 1 < s.len() && s[pos] == 'v' && s[pos+1] == 'v' { rest + 1 } else { rest }
    }
}

spec fn wow_factor_sum(s: Seq<char>, pos: int) -> int
    decreases s.len() - pos
{
    if pos >= s.len() { 0 }
    else {
        let current = if s[pos] == 'o' { 
            count_vv_pairs_before(s, pos) * count_vv_pairs_after(s, pos + 1)
        } else { 0 };
        current + wow_factor_sum(s, pos + 1)
    }
}
// </vc-preamble>

// <vc-helpers>
pub open spec fn int_to_nat_option(i: int) -> std::option::Option<vstd::prelude::nat>
{
    if i >= 0 { Option::Some(i as nat) } else { Option::None }
}
pub open spec fn reversed_range(start: int, end: int) -> Seq<int> {
    if start >= end {
        Seq::new(0, |i: nat| 0) // Fixed: Seq::new takes two arguments (length, and a closure to initialize elements)
    } else {
        reversed_range(start + 1, end).push(start)
    }
}
// </vc-helpers>

// <vc-spec>
fn solve(s: Vec<char>) -> (result: i8)
    ensures
        result as int == wow_factor(s@)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Fixed type mismatch in `right_vv_counts.set(i as u32, count)` by casting `i` to `usize` for indexing. */
{
    if s.len() < 4 {
        return 0i8;
    }

    let s_len: usize = s.len();
    let mut total_wow: i8 = 0;
    let mut current_vv_left: u32 = 0;

    let mut right_vv_counts: Vec<u32> = Vec::new();
    let mut k: usize = 0;
    while k < s_len + 1
        invariant
            0 <= k,
            k <= s_len + 1,
            right_vv_counts.len() == k,
    {
        right_vv_counts.push(0);
        k = k + 1;
    }

    let mut last_char: char = ' ';
    let mut count: u32 = 0;
    let mut i: usize = s_len - 1;

    while i > 0
        invariant
            i < s_len,
            right_vv_counts.len() == s_len + 1,
            count >= 0,
    {
        let cur_char = s[i];

        if cur_char == 'v' && last_char == 'v' {
            count = count + 1;
        }
        right_vv_counts.set(i, count); 
        last_char = cur_char;
        i = i - 1;
    }
    // Handle the 0th index if not handled by the loop
    if s_len >= 1 {
        let cur_char = s[0];
        if cur_char == 'v' && last_char == 'v' {
            count = count + 1;
        }
        right_vv_counts.set(0, count);
    }

    let mut j: usize = 0;
    while j < s_len
        invariant
            0 <= j,
            j <= s_len,
            right_vv_counts.len() == s_len + 1,
            total_wow >= 0,
            current_vv_left >= 0,
    {
        let cur_char = s[j];
        if j >= 1 && cur_char == 'v' && s[j - 1] == 'v' {
            current_vv_left = current_vv_left + 1;
        }

        if cur_char == 'o' {
            let vv_right = if (j + 1) < s_len {
                right_vv_counts[j + 1]
            } else {
                0
            };
            total_wow = total_wow + (current_vv_left as i8) * (vv_right as i8);
        }
        j = j + 1;
    }

    total_wow
}
// </vc-code>


}

fn main() {}