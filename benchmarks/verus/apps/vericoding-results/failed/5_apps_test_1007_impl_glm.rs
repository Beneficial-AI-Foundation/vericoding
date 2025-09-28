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
fn exec_int_to_string(n: nat) -> (s: Seq<char>)
    decreases n
{
    if n == 0 {
        seq!['0']
    } else if n < 10 {
        let c = ('0' as int + n) as char;
        seq![c]
    } else {
        let last_digit = n % 10;
        let rest = n / 10;
        let s_rest = exec_int_to_string(rest);
        let c = ('0' as int + last_digit) as char;
        s_rest.add(seq![c])
    }
}

proof fn lemma_exec_int_to_string(n: nat)
    decreases n
    ensures exec_int_to_string(n) == int_to_string(n as int)
{
    if n == 0 {
        assert(exec_int_to_string(n) =~= seq!['0']);
        assert(int_to_string(0) =~= seq!['0']);
    } else if n < 10 {
        let c = ('0' as int + n) as char;
        assert(exec_int_to_string(n) =~= seq![c]);
        assert(int_to_string(n as int) =~= seq![c]);
    } else {
        let last_digit = n % 10;
        let rest = n / 10;
        lemma_exec_int_to_string(rest);
        let s_rest = exec_int_to_string(rest);
        let c = ('0' as int + last_digit) as char;
        assert(exec_int_to_string(n) =~= s_rest.add(seq![c]));
        assert(int_to_string(n as int) =~= int_to_string(rest as int).add(seq![c]));
    }
}

fn exec_reverse_string(s: Seq<char>) -> (t: Seq<char>)
    decreases s.len()
{
    if s.len() == 0 {
        seq![]
    } else {
        let reversed_rest = exec_reverse_string(s.subrange(1, s.len() as int));
        reversed_rest.add(seq![s[0]])
    }
}

proof fn lemma_exec_reverse_string(s: Seq<char>)
    decreases s.len()
    ensures exec_reverse_string(s) == reverse_string(s)
{
    if s.len() == 0 {
        assert(exec_reverse_string(s) =~= seq![]);
        assert(reverse_string(s) =~= seq![]);
    } else {
        lemma_exec_reverse_string(s.subrange(1, s.len() as int));
        let reversed_rest = exec_reverse_string(s.subrange(1, s.len() as int));
        assert(exec_reverse_string(s) =~= reversed_rest.add(seq![s[0]]));
        assert(reverse_string(s) =~= reverse_string(s.subrange(1, s.len() as int)).add(seq![s[0]]));
    }
}

fn exec_string_to_int(s: Seq<char>) -> (n: nat)
    decreases s.len()
{
    if s.len() == 0 {
        0
    } else if s.len() == 1 {
        (s[0] as int) - ('0' as int)
    } else {
        let first_part = s.subrange(0, s.len()-1);
        let last_char = s[s.len()-1];
        let first_part_int = exec_string_to_int(first_part);
        let last_digit = (last_char as int) - ('0' as int);
        first_part_int * 10 + last_digit
    }
}

proof fn lemma_exec_string_to_int(s: Seq<char>)
    decreases s.len()
    ensures exec_string_to_int(s) == string_to_int(s)
{
    if s.len() == 0 {
        assert(exec_string_to_int(s) == 0);
        assert(string_to_int(s) == 0);
    } else if s.len() == 1 {
        let digit = (s[0] as int) - ('0' as int);
        assert(exec_string_to_int(s) == digit);
        assert(string_to_int(s) == digit);
    } else {
        let first_part = s.subrange(0, s.len()-1);
        lemma_exec_string_to_int(first_part);
        let first_part_int = exec_string_to_int(first_part);
        let last_digit = (s[s.len()-1] as int) - ('0' as int);
        assert(exec_string_to_int(s) == first_part_int * 10 + last_digit);
        assert(string_to_int(s) == string_to_int(first_part) * 10 + last_digit);
    }
}

fn exec_sum_of_palindromes(k: nat) -> (total: nat)
    decreases k
{
    if k == 0 {
        0
    } else {
        let s = exec_int_to_string(k);
        let reversed = exec_reverse_string(s);
        let palindrome_str = s.add(reversed);
        let palindrome_num = exec_string_to_int(palindrome_str);
        palindrome_num + exec_sum_of_palindromes(k-1)
    }
}

proof fn lemma_exec_sum_of_palindromes(k: nat)
    decreases k
    ensures exec_sum_of_palindromes(k) == sum_of_palindromes(k as int)
{
    if k == 0 {
        assert(exec_sum_of_palindromes(k) == 0);
        assert(sum_of_palindromes(0) == 0);
    } else {
        lemma_exec_sum_of_palindromes(k-1);
        let s = exec_int_to_string(k);
        lemma_exec_int_to_string(k);
        let reversed = exec_reverse_string(s);
        lemma_exec_reverse_string(s);
        let palindrome_str = s.add(reversed);
        let palindrome_num = exec_string_to_int(palindrome_str);
        lemma_exec_string_to_int(palindrome_str);
        let spec_s = int_to_string(k as int);
        let spec_reversed = reverse_string(spec_s);
        let spec_palindrome_str = spec_s.add(spec_reversed);
        let spec_palindrome_num = string_to_int(spec_palindrome_str);
        assert(palindrome_num == spec_palindrome_num);
        assert(exec_sum_of_palindromes(k) == palindrome_num + exec_sum_of_palindromes(k-1));
        assert(sum_of_palindromes(k as int) == spec_palindrome_num + sum_of_palindromes(k-1 as int));
        assert(exec_sum_of_palindromes(k-1) == sum_of_palindromes(k-1 as int));
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
{
    let k_nat = k as nat;
    let total_nat = exec_sum_of_palindromes(k_nat);
    let total_int = total_nat as int;
    let remainder_int = total_int % (p as int);
    let result = remainder_int as i8;

    lemma_exec_sum_of_palindromes(k_nat);

    // Prove the ensures clauses
    assert(0 <= remainder_int < p);
    assert(result as int == remainder_int);

    // Therefore, we have:
    //   0 <= result < p
    //   result as int == (sum_of_palindromes(k as int) % (p as int))

    result
}
// </vc-code>


}
fn main() {}