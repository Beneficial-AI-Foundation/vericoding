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
/* helper modified by LLM (iteration 4): convert a natural number to its binary Seq<char> representation */
spec fn Nat2Bits(n: nat) -> Seq<char>
    decreases n
{
    if n == 0 {
        Seq::<char>::empty()
    } else {
        let q = n / 2;
        let r = n % 2;
        if r == 0 { Nat2Bits(q).push('0') } else { Nat2Bits(q).push('1') }
    }
}

/* helper modified by LLM (iteration 4): lemma showing pushing a valid bit preserves validity */
proof fn lemma_ValidBitString_push(s: Seq<char>, c: char)
    requires
        ValidBitString(s),
        c == '0' || c == '1',
    ensures
        ValidBitString(s.push(c))
{
    assert_forall_by(|i: int| {
        requires 0 <= i && i < s.push(c).len() as int;
        ensures s.push(c).index(i) == '0' || s.push(c).index(i) == '1';
        if i < s.len() as int {
            assert(0 <= i && i < s.len() as int);
            assert(s.index(i) == '0' || s.index(i) == '1');
            assert(s.push(c).index(i) == s.index(i));
        } else {
            assert(s.push(c).len() == s.len() + 1);
            assert(i == s.len() as int);
            assert(s.push(c).index(i) == c);
        }
    });
}

/* helper modified by LLM (iteration 4): lemma proving Str2Int(Nat2Bits(n)) == n and validity */
proof fn lemma_Nat2Bits_correct(n: nat)
    ensures
        ValidBitString(Nat2Bits(n)),
        Str2Int(Nat2Bits(n)) == n,
    decreases n
{
    if n == 0 {
        assert(Str2Int(Nat2Bits(0)) == 0);
        assert(ValidBitString(Nat2Bits(0)));
    } else {
        let q = n / 2;
        let r = n % 2;
        lemma_Nat2Bits_correct(q);
        let s = Nat2Bits(q);
        let c: char = if r == 0 { '0' } else { '1' };
        lemma_ValidBitString_push(s, c);
        assert(Nat2Bits(n) == if r == 0 { s.push('0') } else { s.push('1') });
        assert(ValidBitString(Nat2Bits(n)));
        let sc = s.push(c);
        assert(sc.len() == s.len() + 1);
        assert(sc.index(sc.len() as int - 1) == c);
        assert(sc.subrange(0, sc.len() as int - 1) == s);
        assert(Str2Int(sc) == 2 * Str2Int(s) + (if c == '1' { 1nat } else { 0nat }));
        assert(Str2Int(s) == q);
        // Basic arithmetic facts about remainder mod 2
        assert(r < 2);
        if r == 0 {
            assert(c == '0');
            assert((if c == '1' { 1nat } else { 0nat }) == 0);
            assert(Str2Int(sc) == 2 * q + 0);
        } else {
            // Here r != 0 and r < 2 with r a nat, hence r == 1
            assert(0 <= r);
            assert(0 < r);
            assert(r <= 1);
            assert(r == 1);
            assert(c == '1');
            assert((if c == '1' { 1nat } else { 0nat }) == 1);
            assert(Str2Int(sc) == 2 * q + 1);
        }
        assert(n == 2 * q + r);
        assert(Str2Int(sc) == n);
        assert(Str2Int(Nat2Bits(n)) == n);
    }
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_int_ModExpPow2_int(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 4): compute modular exponent via spec and convert to bits using helpers */
{
    let bx = Str2Int(sx@);
    let by = Str2Int(sy@);
    let m = Str2Int(sz@);
    let n = Exp_int(bx, by) % m;
    proof { lemma_Nat2Bits_correct(n); }
    let res = Nat2Bits(n).to_vec();
    res
}
// </vc-code>

fn main() {}
}
