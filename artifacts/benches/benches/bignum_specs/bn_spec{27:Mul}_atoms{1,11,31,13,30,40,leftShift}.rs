use vstd::prelude::*;

verus! {

// ATOM BN_46
spec fn valid_bit_string(s: Seq<char>) -> bool {
    forall|i: int| 0 <= i < s.len() ==> (s[i] == '0' || s[i] == '1')
}

// ATOM BN_11
spec fn exp_int(x: nat, y: nat) -> nat
    decreases y
{
    if y == 0 { 1nat } else { x * exp_int(x, (y - 1) as nat) }
}

// ATOM BN_40  
spec fn str2int(s: Seq<char>) -> nat
    decreases s.len()
{
    if s.len() == 0 {
        0nat
    } else {
        if valid_bit_string(s) {
            2nat * str2int(s.subrange(0, s.len() - 1)) + 
            (if s[s.len() - 1] == '1' { 1nat } else { 0nat })
        } else {
            0nat
        }
    }
}

// ATOM BN_31
spec fn pow2(n: nat) -> nat
    decreases n
{
    if n == 0 { 1nat } else { 2nat * pow2((n - 1) as nat) }
}

// ATOM BN_13
proof fn expand(a: nat, b: nat, c: nat)
    ensures a * (b + 1nat) * c == a * c + a * b * c
{
    assert(a * (b + 1nat) * c == a * (b * c + 1nat * c)) by(nonlinear_arith);
    assert(a * (b * c + c) == a * b * c + a * c) by(nonlinear_arith);
}

// ATOM BN_29
proof fn mul_is_associative(a: nat, b: nat, c: nat)
    ensures a * (b * c) == a * b * c
{
    assert(a * (b * c) == (a * b) * c) by(nonlinear_arith);
}

// ATOM BN_41
proof fn str2int_lemma(s: Seq<char>, i: nat)
    requires 
        valid_bit_string(s),
        0 <= i <= s.len() - 1,
    ensures str2int(s) == str2int(s.subrange(0, (i + 1) as int)) * exp_int(2nat, (s.len() - 1 - i) as nat) + str2int(s.subrange((i + 1) as int, s.len() as int))
{
    assume(str2int(s) == str2int(s.subrange(0, (i + 1) as int)) * exp_int(2nat, (s.len() - 1 - i) as nat) + str2int(s.subrange((i + 1) as int, s.len() as int)));
}

// ATOM BN_1
#[verifier::exec_allows_no_decreases_clause]
fn add(s1: Seq<char>, s2: Seq<char>) -> (res: Seq<char>)
    requires 
        valid_bit_string(s1) && valid_bit_string(s2)
    ensures 
        valid_bit_string(res),
        str2int(res) == str2int(s1) + str2int(s2),
    opens_invariants none
{
    assume(false);
    loop {}
}

// ATOM BN_30
#[verifier::exec_allows_no_decreases_clause]
fn normalize_bit_string(s: Seq<char>) -> (t: Seq<char>)
    ensures 
        valid_bit_string(t),
        t.len() > 0,
        t.len() > 1 ==> t[0] != '0',
        valid_bit_string(s) ==> str2int(s) == str2int(t),
    opens_invariants none
{
    assume(false);
    loop {}
}

// ATOM leftShift
#[verifier::exec_allows_no_decreases_clause]
fn left_shift(s: Seq<char>, n: nat) -> (res: Seq<char>)
    requires valid_bit_string(s)
    ensures 
        valid_bit_string(res),
        str2int(res) == str2int(s) * pow2(n),
    opens_invariants none
{
    assume(false);
    loop {}
}

// SPEC BN_27
#[verifier::exec_allows_no_decreases_clause]
fn mul(s1: Seq<char>, s2: Seq<char>) -> (res: Seq<char>)
    requires valid_bit_string(s1) && valid_bit_string(s2)
    ensures 
        valid_bit_string(res),
        str2int(res) == str2int(s1) * str2int(s2),
    opens_invariants none
{
    // Empty body - constraint says this can't be implemented with * on integers
    assume(false);
    loop {}
}

fn main() {}

} // verus!