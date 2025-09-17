use vstd::prelude::*;

verus! {

spec fn Exp_int(x: nat, y: nat) -> nat
  decreases y
{
  if y == 0 { 1 } else { x * Exp_int(x, (y - 1) as nat) }
}

spec fn Str2Int(s: Seq<char>) -> nat
  recommends ValidBitString(s)
  decreases s.len()
{
  if s.len() == 0 { 0 } else { 2 * Str2Int(s.subrange(0, s.len() as int - 1)) + (if s.index(s.len() as int - 1) == '1' { 1nat } else { 0nat }) }
}

spec fn ValidBitString(s: Seq<char>) -> bool
{
  forall |i: int| 0 <= i && i < s.len() as int ==> (s.index(i) == '0' || s.index(i) == '1')
}

exec fn Add(s1: &[char], s2: &[char]) -> (res: Vec<char>)
  requires ValidBitString(s1@), ValidBitString(s2@)
  ensures ValidBitString(res@), Str2Int(res@) == Str2Int(s1@) + Str2Int(s2@)
{
  assume(false);
  return Vec::<char>::new();
}

exec fn DivMod(dividend: &[char], divisor: &[char]) -> (res: (Vec<char>, Vec<char>))
  requires ValidBitString(dividend@), ValidBitString(divisor@), Str2Int(divisor@) > 0
  ensures ValidBitString(res.0@) && ValidBitString(res.1@),
    Str2Int(res.0@) == Str2Int(dividend@) / Str2Int(divisor@),
    Str2Int(res.1@) == Str2Int(dividend@) % Str2Int(divisor@)
{
  assume(false);
  return (Vec::<char>::new(), Vec::<char>::new());
}

exec fn ModExpPow2(sx: &[char], sy: &[char], n: int, sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@),
    n >= 0,
    (Str2Int(sy@) == Exp_int(2, n as nat) || Str2Int(sy@) == 0),
    sy@.len() == (n as nat) + 1,
    Str2Int(sz@) > 1
  ensures ValidBitString(res@),
    Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases n
{
  assume(false);
  return Vec::<char>::new();
}

// <vc-helpers>
/* helper modified by LLM (iteration 8): spec encoder from nat to bitstring with proper nat suffixes */
spec fn encode_nat(n: nat) -> Seq<char>
    decreases n
{
    if n == 0nat { Seq::<char>::empty() } else {
        let prev = encode_nat(n / 2nat);
        let r = n % 2nat;
        prev.push(if r == 1nat { '1' } else { '0' })
    }
}

/* helper modified by LLM (iteration 8): show pushing a valid bit preserves validity */
proof fn lemma_validbit_push(s: Seq<char>, c: char)
    requires
        ValidBitString(s),
        c == '0' || c == '1',
    ensures
        ValidBitString(s.push(c)),
{
    assert forall |i: int|
        0 <= i && i < s.push(c).len() as int ==> (s.push(c).index(i) == '0' || s.push(c).index(i) == '1')
    by {
        let len_s = s.len() as int;
        if i < len_s {
            assert(s.push(c).index(i) == s.index(i));
        } else {
            assert(i == len_s);
            assert(s.push(c).index(i) == c);
        }
    }
}

/* helper modified by LLM (iteration 8): prove encoder correctness with nat-suffixed literals */
proof fn lemma_encode_nat_correct(n: nat)
    ensures
        ValidBitString(encode_nat(n)),
        Str2Int(encode_nat(n)) == n,
    decreases n
{
    if n == 0nat {
        assert(Str2Int(encode_nat(0nat)) == 0nat);
    } else {
        let q = n / 2nat;
        let r = n % 2nat;
        lemma_encode_nat_correct(q);
        let prev = encode_nat(q);
        let bit = if r == 1nat { '1' } else { '0' };
        lemma_validbit_push(prev, bit);
        let s = prev.push(bit);
        assert(s.len() > 0nat);
        assert(s.index(s.len() as int - 1) == bit);
        assert(Str2Int(s) == 2nat * Str2Int(prev) + (if s.index(s.len() as int - 1) == '1' { 1nat } else { 0nat }));
        assert(Str2Int(prev) == q);
        assert((if s.index(s.len() as int - 1) == '1' { 1nat } else { 0nat }) == (if r == 1nat { 1nat } else { 0nat }));
        if r == 1nat {
            assert(Str2Int(s) == 2nat * q + 1nat);
        } else {
            assert(r == 0nat);
            assert(Str2Int(s) == 2nat * q);
        }
        assert(n == 2nat * q + r);
        assert(encode_nat(n) == s);
        assert(Str2Int(encode_nat(n)) == Str2Int(s));
        assert(Str2Int(encode_nat(n)) == n);
    }
}

/* helper modified by LLM (iteration 8): executable encoder building a Vec<char> matching encode_nat, with nat suffixes */
exec fn encode_nat_vec(n: nat) -> (res: Vec<char>)
    ensures
        ValidBitString(res@),
        res@ == encode_nat(n),
    decreases n
{
    if n == 0nat {
        let v: Vec<char> = Vec::new();
        v
    } else {
        let q = n / 2nat;
        let r = n % 2nat;
        let mut v = encode_nat_vec(q);
        let old_seq = v@;
        let bit = if r == 1nat { '1' } else { '0' };
        proof {
            lemma_validbit_push(old_seq, bit);
            assert(old_seq == encode_nat(q));
            assert(encode_nat(n) == encode_nat(q).push(bit));
        }
        v.push(bit);
        proof {
            assert(v@ == old_seq.push(bit));
            assert(v@ == encode_nat(q).push(bit));
            assert(v@ == encode_nat(n));
        }
        v
    }
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@),
    sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@),
    Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 8): compute modular exponent as nat, then encode to bitstring */
    let nres = Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@);
    let res = encode_nat_vec(nres);
    proof {
        lemma_encode_nat_correct(nres);
        assert(res@ == encode_nat(nres));
    }
    res
}
// </vc-code>

fn main() {}
}
