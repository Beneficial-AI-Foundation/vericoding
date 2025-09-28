// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn int_to_string(n: int) -> Seq<char>
    decreases n
{
    if n == 0 {
        seq!['0']
    } else if n < 10 {
        seq![('0' as int + n) as char]
    } else {
        int_to_string(n / 10).add(seq![('0' as int + (n % 10)) as char])
    }
}

spec fn reverse_string(s: Seq<char>) -> Seq<char>
    decreases s.len()
{
    if s.len() == 0 {
        seq![]
    } else {
        reverse_string(s.subrange(1, s.len() as int)).add(seq![s[0]])
    }
}

spec fn string_to_int(s: Seq<char>) -> int
    decreases s.len()
{
    if s.len() == 0 {
        0
    } else if s.len() == 1 {
        (s[0] as int) - ('0' as int)
    } else {
        string_to_int(s.subrange(0, s.len() - 1)) * 10 + ((s[s.len() - 1] as int) - ('0' as int))
    }
}

spec fn sum_of_palindromes(k: int) -> int
    decreases k
{
    if k <= 0 {
        0
    } else if k == 1 {
        let s = int_to_string(1);
        let reversed = reverse_string(s);
        let palindrome = s.add(reversed);
        string_to_int(palindrome)
    } else {
        let s = int_to_string(k);
        let reversed = reverse_string(s);
        let palindrome = s.add(reversed);
        string_to_int(palindrome) + sum_of_palindromes(k - 1)
    }
}

spec fn valid_input(k: int, p: int) -> bool {
    k >= 1 && p >= 1
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Clean up helper proofs with proper verus syntax */
proof fn lemma_sum_of_palindromes_mod_property(k: int, p: int)
    requires
        k >= 1,
        p >= 1,
    ensures
        (sum_of_palindromes(k) % p) >= 0 < p,
{
    if k > 1 {
        lemma_sum_of_palindromes_mod_property(k - 1, p);
    }
}

proof fn compute_palindrome_value(n: int) -> (result: int)
    requires
        n >= 1,
    ensures
        result == string_to_int(int_to_string(n).add(reverse_string(int_to_string(n)))),
{
    let s = int_to_string(n);
    let reversed = reverse_string(s);
    let combined = s.add(reversed);
    string_to_int(combined)
}

proof fn compute_sum_of_palindromes_recursive(k: int, p: int) -> (result: int)
    requires
        k >= 1,
        p >= 1,
    ensures
        result == sum_of_palindromes(k) % p,
        result >= 0 < p,
    decreases k
{
    if k == 1 {
        let palindrome = compute_palindrome_value(1);
        palindrome % p
    } else {
        let prev_sum_mod = compute_sum_of_palindromes_recursive(k - 1, p);
        let current_palindrome = compute_palindrome_value(k);
        (prev_sum_mod + current_palindrome) % p
    }
}
// </vc-helpers>

// <vc-spec>
fn solve(k: i8, p: i8) -> (result: i8)
    requires
        valid_input(k as int, p as int),
    ensures
        0 <= result < p,
        result as int == (sum_of_palindromes(k as int) % (p as int)),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Fix ghost variable syntax and return proper value */
{
    proof {
        let ghost_k = k as int;
        let ghost_p = p as int;
        lemma_sum_of_palindromes_mod_property(ghost_k, ghost_p);
        let mod_result = compute_sum_of_palindromes_recursive(ghost_k, ghost_p);
        assert(mod_result == sum_of_palindromes(ghost_k) % ghost_p);
        assert(0 <= mod_result < ghost_p);
        (mod_result as i8)
    }
}
// </vc-code>


}
fn main() {}