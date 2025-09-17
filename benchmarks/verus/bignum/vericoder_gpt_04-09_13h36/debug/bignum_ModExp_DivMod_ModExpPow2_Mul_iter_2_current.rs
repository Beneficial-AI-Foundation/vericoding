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
proof fn lemma_Str2Int_push(s: Seq<char>, b: char)
    ensures
        Str2Int(s.push(b)) == 2 * Str2Int(s) + (if b == '1' { 1 } else { 0 })
{
    let sp = s.push(b);
    assert(sp.len() > 0);
    assert(sp.len() as int - 1 == s.len() as int);
    assert(sp.subrange(0, sp.len() as int - 1) == s);
    assert(sp.index(sp.len() as int - 1) == b);
    assert(
        Str2Int(sp)
        == 2 * Str2Int(sp.subrange(0, sp.len() as int - 1))
            + (if sp.index(sp.len() as int - 1) == '1' { 1 } else { 0 })
    );
}

spec fn Nat2BitSeq(n: nat) -> Seq<char>
    decreases n
{
    if n == 0 {
        Seq::<char>::empty()
    } else {
        let q = n / 2;
        let r = n % 2;
        Nat2BitSeq(q).push(if r == 1 { '1' } else { '0' })
    }
}

proof fn lemma_Nat2BitSeq_correct(n: nat)
    ensures
        ValidBitString(Nat2BitSeq(n)),
        Str2Int(Nat2BitSeq(n)) == n
    decreases n
{
    if n == 0 {
        // Nat2BitSeq(0) = empty
        assert(ValidBitString(Seq::<char>::empty()));
        assert(Str2Int(Seq::<char>::empty()) == 0);
    } else {
        let q = n / 2;
        let r = n % 2;
        // 0 <= r < 2 and n = 2*q + r
        assert(0 <= r && r < 2);
        assert(n == 2 * q + r);

        // IH on q
        lemma_Nat2BitSeq_correct(q);

        let b = if r == 1 { '1' } else { '0' };
        let s = Nat2BitSeq(q);
        let sp = s.push(b);

        // Prove ValidBitString(sp)
        assert(forall |i: int|
            0 <= i && i < sp.len() as int ==> #[trigger] sp.index(i) == '0' || sp.index(i) == '1'
        ) by {
            assert forall |i: int|
                0 <= i && i < sp.len() as int ==> #[trigger] sp.index(i) == '0' || sp.index(i) == '1'
            by {
                if i < s.len() as int {
                    assert(sp.index(i) == s.index(i));
                    assert(ValidBitString(s));
                    assert(s.index(i) == '0' || s.index(i) == '1');
                } else {
                    assert(sp.len() == s.len() + 1);
                    assert(i == s.len() as int);
                    assert(sp.index(i) == b);
                    if r == 1 {
                        assert(b == '1');
                    } else {
                        assert(b == '0');
                    }
                }
            }
        }

        // Prove Str2Int(sp) = n
        lemma_Str2Int_push(s, b);
        if r == 1 {
            assert(b == '1');
            assert(Str2Int(sp) == 2 * Str2Int(s) + 1);
            assert(Str2Int(s) == q);
            assert(Str2Int(sp) == 2 * q + 1);
            assert(Str2Int(Nat2BitSeq(n)) == n);
        } else {
            assert(r == 0);
            assert(b == '
// </vc-helpers>

// <vc-spec>
exec fn ModExp_DivMod_ModExpPow2_Mul(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
proof fn lemma_Str2Int_push(s: Seq<char>, b: char)
    ensures
        Str2Int(s.push(b)) == 2 * Str2Int(s) + (if b == '1' { 1 } else { 0 })
{
    let sp = s.push(b);
    assert(sp.len() > 0);
    assert(sp.len() as int - 1 == s.len() as int);
    assert(sp.subrange(0, sp.len() as int - 1) == s);
    assert(sp.index(sp.len() as int - 1) == b);
    assert(
        Str2Int(sp)
        == 2 * Str2Int(sp.subrange(0, sp.len() as int - 1))
            + (if sp.index(sp.len() as int - 1) == '1' { 1 } else { 0 })
    );
}

spec fn Nat2BitSeq(n: nat) -> Seq<char>
    decreases n
{
    if n == 0 {
        Seq::<char>::empty()
    } else {
        let q = n / 2;
        let r = n % 2;
        Nat2BitSeq(q).push(if r == 1 { '1' } else { '0' })
    }
}

proof fn lemma_Nat2BitSeq_correct(n: nat)
    ensures
        ValidBitString(Nat2BitSeq(n)),
        Str2Int(Nat2BitSeq(n)) == n
    decreases n
{
    if n == 0 {
        // Nat2BitSeq(0) = empty
        assert(ValidBitString(Seq::<char>::empty()));
        assert(Str2Int(Seq::<char>::empty()) == 0);
    } else {
        let q = n / 2;
        let r = n % 2;
        // 0 <= r < 2 and n = 2*q + r
        assert(0 <= r && r < 2);
        assert(n == 2 * q + r);

        // IH on q
        lemma_Nat2BitSeq_correct(q);

        let b = if r == 1 { '1' } else { '0' };
        let s = Nat2BitSeq(q);
        let sp = s.push(b);

        // Prove ValidBitString(sp)
        assert(forall |i: int|
            0 <= i && i < sp.len() as int ==> #[trigger] sp.index(i) == '0' || sp.index(i) == '1'
        ) by {
            assert forall |i: int|
                0 <= i && i < sp.len() as int ==> #[trigger] sp.index(i) == '0' || sp.index(i) == '1'
            by {
                if i < s.len() as int {
                    assert(sp.index(i) == s.index(i));
                    assert(ValidBitString(s));
                    assert(s.index(i) == '0' || s.index(i) == '1');
                } else {
                    assert(sp.len() == s.len() + 1);
                    assert(i == s.len() as int);
                    assert(sp.index(i) == b);
                    if r == 1 {
                        assert(b == '1');
                    } else {
                        assert(b == '0');
                    }
                }
            }
        }

        // Prove Str2Int(sp) = n
        lemma_Str2Int_push(s, b);
        if r == 1 {
            assert(b == '1');
            assert(Str2Int(sp) == 2 * Str2Int(s) + 1);
            assert(Str2Int(s) == q);
            assert(Str2Int(sp) == 2 * q + 1);
            assert(Str2Int(Nat2BitSeq(n)) == n);
        } else {
            assert(r == 0);
            assert(b == '
// </vc-code>

fn main() {}
}