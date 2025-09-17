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

// <vc-helpers>
proof fn lemma_div2_identity(n: nat)
    ensures n == 2 * (n / 2) + (n % 2)
{
}

spec fn Nat2Bits(n: nat) -> Seq<char>
    decreases n
{
    if n == 0 {
        Seq::<char>::empty()
    } else {
        let q = n / 2;
        let r = n % 2;
        Nat2Bits(q) + seq![if r == 1 { '1' } else { '0' }]
    }
}

proof fn lemma_nat2bits_valid(n: nat)
    ensures ValidBitString(Nat2Bits(n))
    decreases n
{
    if n == 0 {
        assert(ValidBitString(Seq::<char>::empty()));
    } else {
        let q = n / 2;
        let r = n % 2;
        lemma_nat2bits_valid(q);
        let s1 = Nat2Bits(q);
        let last = if r == 1 { '1' } else { '0' };
        let s = s1 + seq![last];
        assert(s.len() == s1.len() + 1);
        assert(forall |i: int|
            0 <= i && i < s.len() ==> (#[trigger] s.index(i) == '0' || #[trigger] s.index(i) == '1')
        ) by {
            assert(s.len() == s1.len() + 1);
            assert forall |i: int| 0 <= i && i < s.len() implies s.index(i) == '0' || s.index(i) == '1' by {
                if i < s1.len() {
                    assert((s1 + seq![last]).index(i) == s1.index(i));
                    assert(0 <= i && i < s1.len());
                    assert(ValidBitString(s1));
                } else {
                    assert(i == s1.len());
                    assert((s1 + seq![last]).index(i) == last);
                    if r == 1 {
                        assert(last == '1');
                    } else {
                        assert(last == '0');
                    }
                }
            }
        }
    }
}

proof fn lemma_str2int_nat2bits(n: nat)
    ensures Str2Int(Nat2Bits(n)) == n
    decreases n
{
    if n == 0 {
        assert(Nat2Bits(0) == Seq::<char>::empty());
        assert(Str2Int(Seq::<char>::empty()) == 0);
    } else {
        let q = n / 2;
        let r = n % 2;
        lemma_str2int_nat2bits(q);
        let s1
// </vc-helpers>

// <vc-spec>
exec fn ModExp_ModExpPow2_Mul(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
proof fn lemma_div2_identity(n: nat)
    ensures n == 2 * (n / 2) + (n % 2)
{
}

spec fn Nat2Bits(n: nat) -> Seq<char>
    decreases n
{
    if n == 0 {
        Seq::<char>::empty()
    } else {
        let q = n / 2;
        let r = n % 2;
        Nat2Bits(q) + seq![if r == 1 { '1' } else { '0' }]
    }
}

proof fn lemma_nat2bits_valid(n: nat)
    ensures ValidBitString(Nat2Bits(n))
    decreases n
{
    if n == 0 {
        assert(ValidBitString(Seq::<char>::empty()));
    } else {
        let q = n / 2;
        let r = n % 2;
        lemma_nat2bits_valid(q);
        let s1 = Nat2Bits(q);
        let last = if r == 1 { '1' } else { '0' };
        let s = s1 + seq![last];
        assert(s.len() == s1.len() + 1);
        assert(forall |i: int|
            0 <= i && i < s.len() ==> (#[trigger] s.index(i) == '0' || #[trigger] s.index(i) == '1')
        ) by {
            assert(s.len() == s1.len() + 1);
            assert forall |i: int| 0 <= i && i < s.len() implies s.index(i) == '0' || s.index(i) == '1' by {
                if i < s1.len() {
                    assert((s1 + seq![last]).index(i) == s1.index(i));
                    assert(0 <= i && i < s1.len());
                    assert(ValidBitString(s1));
                } else {
                    assert(i == s1.len());
                    assert((s1 + seq![last]).index(i) == last);
                    if r == 1 {
                        assert(last == '1');
                    } else {
                        assert(last == '0');
                    }
                }
            }
        }
    }
}

proof fn lemma_str2int_nat2bits(n: nat)
    ensures Str2Int(Nat2Bits(n)) == n
    decreases n
{
    if n == 0 {
        assert(Nat2Bits(0) == Seq::<char>::empty());
        assert(Str2Int(Seq::<char>::empty()) == 0);
    } else {
        let q = n / 2;
        let r = n % 2;
        lemma_str2int_nat2bits(q);
        let s1
// </vc-code>

fn main() {}
}