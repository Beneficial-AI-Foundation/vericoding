// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_lucky_number(n: Seq<char>) -> bool {
    n.len() > 0 && forall|i: int| 0 <= i < n.len() ==> n[i] == '4' || n[i] == '7'
}

spec fn convert_to_binary(n: Seq<char>) -> Seq<char>
    recommends forall|i: int| 0 <= i < n.len() ==> n[i] == '4' || n[i] == '7'
    decreases n.len()
{
    if n.len() == 0 {
        Seq::empty()
    } else if n[0] == '4' {
        seq!['0'].add(convert_to_binary(n.subrange(1, n.len() as int)))
    } else {
        seq!['1'].add(convert_to_binary(n.subrange(1, n.len() as int)))
    }
}

spec fn pow2(n: nat) -> nat
    decreases n
{
    if n == 0 { 1 } else { 2 * pow2((n - 1) as nat) }
}

spec fn binary_to_int(s: Seq<char>) -> int
    recommends forall|i: int| 0 <= i < s.len() ==> s[i] == '0' || s[i] == '1'
    decreases s.len()
{
    if s.len() == 0 {
        0
    } else if s[0] == '1' {
        pow2((s.len() - 1) as nat) + binary_to_int(s.subrange(1, s.len() as int))
    } else {
        binary_to_int(s.subrange(1, s.len() as int))
    }
}

spec fn valid_result(n: Seq<char>, result: int) -> bool
    recommends valid_lucky_number(n)
{
    result > 0 && result == 2 * (pow2((n.len() - 1) as nat) - 1) + binary_to_int(convert_to_binary(n)) + 1
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed preconditions for recursive calls and postcondition proof */
proof fn lemma_pow2_positive(n: nat)
    ensures pow2(n) > 0
    decreases n
{
    if n == 0 {
    } else {
        lemma_pow2_positive((n - 1) as nat);
    }
}

proof fn lemma_binary_to_int_bounds(s: Seq<char>)
    requires forall|i: int| 0 <= i < s.len() ==> s[i] == '0' || s[i] == '1'
    ensures 0 <= binary_to_int(s) < pow2(s.len() as nat)
    decreases s.len()
{
    if s.len() == 0 {
    } else {
        lemma_binary_to_int_bounds(s.subrange(1, s.len() as int));
        lemma_pow2_positive((s.len() - 1) as nat);
    }
}

proof fn lemma_subrange_valid_lucky(n: Seq<char>)
    requires valid_lucky_number(n),
             n.len() > 0
    ensures valid_lucky_number(n.subrange(1, n.len() as int))
{
}

proof fn lemma_convert_to_binary_valid(n: Seq<char>)
    requires valid_lucky_number(n)
    ensures forall|i: int| 0 <= i < convert_to_binary(n).len() ==> convert_to_binary(n)[i] == '0' || convert_to_binary(n)[i] == '1'
    decreases n.len()
{
    if n.len() == 0 {
    } else {
        lemma_subrange_valid_lucky(n);
        lemma_convert_to_binary_valid(n.subrange(1, n.len() as int));
        assert(convert_to_binary(n)[0] == '0' || convert_to_binary(n)[0] == '1');
    }
}

proof fn lemma_convert_preserves_length(n: Seq<char>)
    requires valid_lucky_number(n)
    ensures convert_to_binary(n).len() == n.len()
    decreases n.len()
{
    if n.len() == 0 {
    } else {
        lemma_subrange_valid_lucky(n);
        lemma_convert_preserves_length(n.subrange(1, n.len() as int));
    }
}
// </vc-helpers>

// <vc-spec>
fn solve(n: Vec<char>) -> (result: i8)
    requires valid_lucky_number(n@)
    ensures valid_result(n@, result as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed type compatibility by using consistent int types */
    proof {
        lemma_convert_to_binary_valid(n@);
        lemma_convert_preserves_length(n@);
        lemma_binary_to_int_bounds(convert_to_binary(n@));
        lemma_pow2_positive((n@.len() - 1) as nat);
    }
    
    let binary_val = binary_to_int(convert_to_binary(n@));
    let len = n.len() as int;
    let prefix_sum = if len == 1 { 0int } else { 2 * (pow2((len - 1) as nat) - 1) };
    
    let result = (prefix_sum + binary_val + 1) as i8;
    
    proof {
        assert(binary_val >= 0);
        assert(binary_val < pow2(len as nat));
        if len > 1 {
            assert(pow2((len - 1) as nat) >= 1);
        }
    }
    
    result
}
// </vc-code>


}

fn main() {}