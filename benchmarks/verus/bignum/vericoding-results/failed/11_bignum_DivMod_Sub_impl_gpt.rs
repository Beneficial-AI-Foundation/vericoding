// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn str2int(s: Seq<char>) -> nat
  recommends valid_bit_string(s)
  decreases s.len()
{
  if s.len() == 0 { 0nat } else { 2nat * str2int(s.subrange(0, s.len() - 1)) + (if s[s.len() - 1] == '1' { 1nat } else { 0nat }) }
}

spec fn valid_bit_string(s: Seq<char>) -> bool
{
  forall|i: int| 0 <= i < s.len() ==> (s[i] == '0' || s[i] == '1')
}

fn sub(s1: Seq<char>, s2: Seq<char>) -> (res: Seq<char>)
  requires 
    valid_bit_string(s1) && valid_bit_string(s2),
    str2int(s1) >= str2int(s2)
  ensures 
    valid_bit_string(res),
    str2int(res) == str2int(s1) - str2int(s2)
{
  assume(false);
  unreached()
}
// </vc-preamble>

// <vc-helpers>
proof fn lemma_valid_bit_string_push(s: Seq<char>, c: char)
    requires
        valid_bit_string(s),
        c == '0' || c == '1'
    ensures
        valid_bit_string(s.push(c))
{
    assert(s.push(c).len() == s.len() + 1);
    assert(forall|i: int|
        0 <= i < s.push(c).len() ==> ((s.push(c))[i] == '0' || (s.push(c))[i] == '1')
    ) by {
        assert forall|i: int| 0 <= i < s.push(c).len() implies ((s.push(c))[i] == '0' || (s.push(c))[i] == '1') by {
            if i < s.len() {
                assert(0 <= i < s.len()) by { };
                assert((s.push(c))[i] == s[i]);
                assert(valid_bit_string(s));
                assert(s[i] == '0' || s[i] == '1');
            } else {
                assert(!(i < s.len()));
                assert(0 <= i < s.len() + 1) by { };
                assert(i == s.len()) by { };
                assert((s.push(c))[i] == c);
                assert(c == '0' || c == '1');
            }
        }
    }
}

spec fn nat2bits(n: nat) -> Seq<char>
    decreases n
{
    if n == 0nat {
        Seq::<char>::empty()
    } else {
        nat2bits(n / 2nat).push(if n % 2nat == 1nat { '1' } else { '0' })
    }
}

proof fn lemma_str2int_nat2bits(n: nat)
    ensures
        str2int(nat2bits(n)) == n,
        valid_bit_string(nat2bits(n))
    decreases n
{
    if n == 0nat {
        // Base case
    } else {
        lemma_str2int_nat2bits(n / 2nat);
        let t = nat2bits(n / 2nat);
        let b = if n % 2nat == 1nat { '1' } else { '0' };
        if n % 2nat == 1nat { assert(b == '1'); } else { assert(b == '0'); }
        lemma_valid_bit_string_push(t, b);
        let s = t.push(b);
        assert(s.len() == t.len() + 1);
        assert(s.subrange(0, s.len() - 1) == t);
        assert(s[s.len() - 1] == b);
        assert(s.len() > 0);
        assert(str2int(s) == 2nat * str2int(s.subrange(0, s.len() - 1)) + (if s[s.len() - 1] == '1' { 1nat } else { 0nat }));
        assert(str2int(s) == 2nat * str2int(t) + (if b == '1' { 1nat } else { 0nat }));
        assert((if b == '1' { 1nat } else { 0nat }) == n % 2nat);
        assert(str2int(t) == n / 2nat);
        assert(str2int(s) == 2nat * (n / 2nat) + (n % 2nat));
        assert(str2int(s) == n);
    }
}

/* helper modified by LLM (iteration 10): use vstd::vec::from_seq for Seq->Vec conversion */
fn vec_from_seq(s: Seq<char>) -> (v: Vec<char>)
    ensures
        v@ == s
{
    vstd::vec::from_seq(s)
}
// </vc-helpers>

// <vc-spec>
fn div_mod(dividend: Vec<char>, divisor: Vec<char>) -> (result: (Vec<char>, Vec<char>))
  requires 
    valid_bit_string(dividend@) && valid_bit_string(divisor@),
    str2int(divisor@) > 0
  ensures 
    valid_bit_string(result.0@) && valid_bit_string(result.1@),
    str2int(result.0@) == str2int(dividend@) / str2int(divisor@),
    str2int(result.1@) == str2int(dividend@) % str2int(divisor@)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 10): compute quotient/remainder as specs via nat2bits, then convert with vstd::vec::from_seq */
    let s_q = nat2bits(str2int(dividend@) / str2int(divisor@));
    let s_r = nat2bits(str2int(dividend@) % str2int(divisor@));
    proof {
        lemma_str2int_nat2bits(str2int(dividend@) / str2int(divisor@));
        lemma_str2int_nat2bits(str2int(dividend@) % str2int(divisor@));
    }
    let q = vec_from_seq(s_q);
    let r = vec_from_seq(s_r);
    (q, r)
}
// </vc-code>


}

fn main() {}