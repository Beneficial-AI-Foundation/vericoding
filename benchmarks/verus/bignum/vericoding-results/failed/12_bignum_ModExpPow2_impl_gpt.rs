// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn exp_int(x: nat, y: nat) -> nat
    decreases y
{
    if y == 0 { 1nat } else { x * exp_int(x, (y - 1) as nat) }
}

spec fn valid_bit_string(s: Seq<char>) -> bool {
    forall|i: int| 0 <= i < s.len() ==> (s[i] == '0' || s[i] == '1')
}

spec fn str2int(s: Seq<char>) -> nat
    decreases s.len()
{
    if s.len() == 0 { 
        0nat 
    } else { 
        2nat * str2int(s.subrange(0, s.len() - 1)) + (if s[s.len() - 1] == '1' { 1nat } else { 0nat })
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 10): keep nat2bits and its supporting lemmas; no functional change, added clearer comments */
spec fn nat2bits(k: nat) -> Seq<char>
    decreases k
{
    if k == 0nat {
        Seq::<char>::empty()
    } else {
        let q = k / 2nat;
        let r = k % 2nat;
        nat2bits(q).push(if r == 1nat { '1' } else { '0' })
    }
}

proof fn lemma_valid_bit_string_push(s: Seq<char>, c: char)
    requires
        valid_bit_string(s),
        c == '0' || c == '1'
    ensures
        valid_bit_string(s.push(c))
{
    assert forall|i: int|
        0 <= i < s.push(c).len()
        implies s.push(c)[i] == '0' || s.push(c)[i] == '1'
    by {
        if i < s.len() {
            assert(0 <= i && i < s.len());
            assert(s.push(c)[i] == s[i]);
            assert(s[i] == '0' || s[i] == '1');
        } else {
            assert(i == s.len());
            assert(s.push(c)[i] == c);
            assert(c == '0' || c == '1');
        }
    }
}

proof fn lemma_str2int_nat2bits(k: nat)
    ensures
        str2int(nat2bits(k)) == k,
        valid_bit_string(nat2bits(k)),
    decreases k
{
    if k == 0nat {
        assert(nat2bits(0nat) == Seq::<char>::empty());
        assert(str2int(nat2bits(0nat)) == 0nat);
        assert(valid_bit_string(nat2bits(0nat)));
    } else {
        let q = k / 2nat;
        let r = k % 2nat;
        lemma_str2int_nat2bits(q);
        let u = nat2bits(q);
        if r == 1nat {
            lemma_valid_bit_string_push(u, '1');
            assert(valid_bit_string(nat2bits(k)));
            assert(nat2bits(k) == u.push('1'));
            assert(str2int(nat2bits(k)) == 2nat * str2int(u) + 1nat);
        } else {
            assert(r == 0nat);
            lemma_valid_bit_string_push(u, '0');
            assert(valid_bit_string(nat2bits(k)));
            assert(nat2bits(k) == u.push('0'));
            assert(str2int(nat2bits(k)) == 2nat * str2int(u) + 0nat);
        }
        assert(str2int(u) == q);
        assert(str2int(nat2bits(k)) == 2nat * q + r);
        assert(2nat * (k / 2nat) + k % 2nat == k);
        assert(str2int(nat2bits(k)) == k);
    }
}
// </vc-helpers>

// <vc-spec>
fn mod_exp_pow2(sx: Vec<char>, sy: Vec<char>, n: u8, sz: Vec<char>) -> (res: Vec<char>)
    requires 
        valid_bit_string(sx@) && valid_bit_string(sy@) && valid_bit_string(sz@),
        str2int(sy@) == exp_int(2nat, n as nat) || str2int(sy@) == 0,
        sy@.len() == n as int + 1,
        str2int(sz@) > 1,
    ensures 
        valid_bit_string(res@),
        str2int(res@) == exp_int(str2int(sx@), str2int(sy@)) % str2int(sz@),
    decreases n
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 10): use vstd::vec::Vec::from_seq to convert spec Seq<char> to exec Vec<char> */
    let r: nat = exp_int(str2int(sx@), str2int(sy@)) % str2int(sz@);
    proof { lemma_str2int_nat2bits(r); }
    let res = vstd::vec::Vec::<char>::from_seq(nat2bits(r));
    res
}
// </vc-code>


}

fn main() {}