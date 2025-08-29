use vstd::prelude::*;

verus! {

// ATOM BN_46
spec fn valid_bit_string(s: Seq<char>) -> bool {
    forall|i: int| 0 <= i < s.len() ==> s[i] == '0' || s[i] == '1'
}

// ATOM BN_11
spec fn exp_int(x: nat, y: nat) -> nat
    decreases y
{
    if y == 0 { 1 } else { x * exp_int(x, (y - 1) as nat) }
}

// ATOM BN_40  
spec fn str2int(s: Seq<char>) -> nat
    decreases s.len()
{
    if s.len() == 0 {
        0
    } else {
        2 * str2int(s.subrange(0, s.len() - 1)) + (if s[s.len() - 1] == '1' { 1 as nat } else { 0 as nat })
    }
}

// ATOM BN_41
proof fn str2int_lemma(s: Seq<char>, i: nat)
    requires 
        valid_bit_string(s),
        0 <= i <= s.len() - 1,
    ensures str2int(s) == str2int(s.subrange(0, (i + 1) as int)) * exp_int(2, ((s.len() - 1 - i) as int) as nat) + str2int(s.subrange((i + 1) as int, s.len() as int))
{
    assume(str2int(s) == str2int(s.subrange(0, (i + 1) as int)) * exp_int(2, ((s.len() - 1 - i) as int) as nat) + str2int(s.subrange((i + 1) as int, s.len() as int)));
}

// ATOM BN_29
proof fn mul_is_associative(a: nat, b: nat, c: nat)
    ensures a * (b * c) == a * b * c
{
    assume(a * (b * c) == a * b * c);
}

// SPEC BN_27
//CONSTRAINTS: don't use * on integers and mapping back to strings for computing the final result
#[verifier::exec_allows_no_decreases_clause]
fn mul(s1: Seq<char>, s2: Seq<char>) -> (res: Seq<char>)
    requires 
        valid_bit_string(s1),
        valid_bit_string(s2),
    ensures 
        valid_bit_string(res),
        str2int(res) == str2int(s1) * str2int(s2),
{
    // Empty method body - specification only like the original Dafny
    loop {
        // This loop never terminates, modeling an unimplemented method
    }
}

}

fn main() {}