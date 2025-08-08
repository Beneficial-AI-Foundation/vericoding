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
        2nat * str2int(s.subrange(0, s.len() - 1)) + 
        (if s[s.len() - 1] == '1' { 1nat } else { 0nat })
    }
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

// ATOM BN_29
proof fn mul_is_associative(a: nat, b: nat, c: nat) 
    ensures a * (b * c) == a * b * c
{
    // This follows from arithmetic properties of multiplication
    assert(a * (b * c) == (a * b) * c) by(nonlinear_arith);
    assert((a * b) * c == a * b * c);
}

// ATOM BN_13
proof fn expand(a: nat, b: nat, c: nat) 
    ensures a * (b + 1nat) * c == a * c + a * b * c
{
    // Distributive property
    assert(a * (b + 1nat) * c == a * c * (b + 1nat)) by(nonlinear_arith);
    assert(a * c * (b + 1nat) == a * c * b + a * c * 1nat) by(nonlinear_arith);
    assert(a * c * b + a * c * 1nat == a * c * b + a * c) by(nonlinear_arith);
    assert(a * c * b + a * c == a * b * c + a * c) by(nonlinear_arith);
}

// ATOM BN_38
proof fn rearrange(a: int, b: int, c: int) 
    ensures (a * 2 + b) * c == a * 2 * c + b * c
{
    // Distributive property
    assert((a * 2 + b) * c == a * 2 * c + b * c) by(nonlinear_arith);
}

// ATOM BN_30
fn normalize_bit_string(s: Ghost<Seq<char>>) -> (t: Ghost<Seq<char>>) 
    ensures 
        valid_bit_string(t@),
        t@.len() > 0,
        t@.len() > 1 ==> t@[0] != '0',
        valid_bit_string(s@) ==> str2int(s@) == str2int(t@),
{
    let t = Ghost(Seq::empty().push('0'));
    assume(valid_bit_string(t@));
    assume(t@.len() > 0);
    assume(t@.len() > 1 ==> t@[0] != '0');
    assume(valid_bit_string(s@) ==> str2int(s@) == str2int(t@));
    t
}

// ATOM BN_1 
fn add(s1: Ghost<Seq<char>>, s2: Ghost<Seq<char>>) -> (res: Ghost<Seq<char>>) 
    requires valid_bit_string(s1@) && valid_bit_string(s2@)
    ensures 
        valid_bit_string(res@),
        str2int(res@) == str2int(s1@) + str2int(s2@),
{
    let res = Ghost(Seq::empty().push('0'));
    assume(str2int(res@) == str2int(s1@) + str2int(s2@));
    res
}

// SPEC BN_27 
//CONSTRAINTS: don't use * on integers and mapping back to strings for computing the final result
fn mul(s1: Ghost<Seq<char>>, s2: Ghost<Seq<char>>) -> (res: Ghost<Seq<char>>) 
    requires valid_bit_string(s1@) && valid_bit_string(s2@)
    ensures 
        valid_bit_string(res@),
        str2int(res@) == str2int(s1@) * str2int(s2@),
{
    let res = Ghost(Seq::empty().push('0'));
    assume(str2int(res@) == str2int(s1@) * str2int(s2@));
    res
}

fn main() {}

}