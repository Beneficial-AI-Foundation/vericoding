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
spec fn Bin(k: nat) -> Seq<char>
    decreases k
{
    if k == 0 {
        Seq::<char>::empty()
    } else {
        let tail = Bin(k / 2);
        tail.push(if k % 2 == 1 { '1' } else { '0' })
    }
}

proof fn lemma_Bin_valid_and_value(k: nat)
    ensures
        ValidBitString(Bin(k)),
        Str2Int(Bin(k)) == k,
    decreases k
{
    if k == 0 {
        // Bin(0) = empty
        assert(ValidBitString(Bin(0)));
        assert(Str2Int(Bin(0)) == 0);
    } else {
        // Inductive step
        lemma_Bin_valid_and_value(k / 2);
        let t = Bin(k / 2);
        let bit = if k % 2 == 1 { '1' } else { '0' };
        let s = t.push(bit);

        // Prove ValidBitString(s)
        assert(ValidBitString(t));
        assert(forall |i: int| 0 <= i && i < s.len() as int ==> #[trigger] (s.index(i) == '0' || s.index(i) == '1')) by {
            assert forall |i: int| 0 <= i && i < s.len() as int implies s.index(i) == '0' || s.index(i) == '1' by {
                let lensi = s.len() as int;
                if i < lensi - 1 {
                    assert(t.len() as int == lensi - 1);
                    assert(0 <= i && i < t.len() as int);
                    assert(#[trigger] (t.index(i) == '0' || t.index(i) == '1'));
                    assert(s.index(i) == t.index(i));
                } else {
                    assert(i == lensi - 1);
                    assert(s.index(lensi - 1) == bit);
                    assert(bit == '0' || bit == '1');
                }
            }
        }

        // Prove Str2Int(s) == k
        let s_len = s.len();
        assert(s_len > 0);
        assert(s.subrange(0, s_len as int - 1)
// </vc-helpers>

// <vc-spec>
exec fn ModExp_int(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
spec fn Bin(k: nat) -> Seq<char>
    decreases k
{
    if k == 0 {
        Seq::<char>::empty()
    } else {
        let tail = Bin(k / 2);
        tail.push(if k % 2 == 1 { '1' } else { '0' })
    }
}

proof fn lemma_Bin_valid_and_value(k: nat)
    ensures
        ValidBitString(Bin(k)),
        Str2Int(Bin(k)) == k,
    decreases k
{
    if k == 0 {
        // Bin(0) = empty
        assert(ValidBitString(Bin(0)));
        assert(Str2Int(Bin(0)) == 0);
    } else {
        // Inductive step
        lemma_Bin_valid_and_value(k / 2);
        let t = Bin(k / 2);
        let bit = if k % 2 == 1 { '1' } else { '0' };
        let s = t.push(bit);

        // Prove ValidBitString(s)
        assert(ValidBitString(t));
        assert(forall |i: int| 0 <= i && i < s.len() as int ==> #[trigger] (s.index(i) == '0' || s.index(i) == '1')) by {
            assert forall |i: int| 0 <= i && i < s.len() as int implies s.index(i) == '0' || s.index(i) == '1' by {
                let lensi = s.len() as int;
                if i < lensi - 1 {
                    assert(t.len() as int == lensi - 1);
                    assert(0 <= i && i < t.len() as int);
                    assert(#[trigger] (t.index(i) == '0' || t.index(i) == '1'));
                    assert(s.index(i) == t.index(i));
                } else {
                    assert(i == lensi - 1);
                    assert(s.index(lensi - 1) == bit);
                    assert(bit == '0' || bit == '1');
                }
            }
        }

        // Prove Str2Int(s) == k
        let s_len = s.len();
        assert(s_len > 0);
        assert(s.subrange(0, s_len as int - 1)
// </vc-code>

fn main() {}
}