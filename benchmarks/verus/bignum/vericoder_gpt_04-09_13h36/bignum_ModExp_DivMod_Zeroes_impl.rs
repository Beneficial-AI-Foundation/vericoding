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
spec fn Int2Str(n: nat) -> Seq<char>
    decreases n
{
    if n == 0 {
        Seq::<char>::empty()
    } else {
        let b = if n % 2 == 1 { '1' } else { '0' };
        Int2Str(n / 2) + seq![b]
    }
}

proof fn lemma_Str2Int_Int2Str(n: nat)
    ensures Str2Int(Int2Str(n)) == n,
            ValidBitString(Int2Str(n))
    decreases n
{
    if n == 0 {
        assert(Str2Int(Seq::<char>::empty()) == 0);
        assert(ValidBitString(Seq::<char>::empty()));
    } else {
        lemma_Str2Int_Int2Str(n / 2);

        let s_prev = Int2Str(n / 2);
        let b = if n % 2 == 1 { '1' } else { '0' };
        let s = s_prev + seq![b];

        // Prove ValidBitString(s)
        assert forall |i:int|
            0 <= i && i < s.len() ==> (s.index(i) == '0' || s.index(i) == '1')
        by {
            if i < s_prev.len() {
                assert(s.index(i) == s_prev.index(i));
                assert(0 <= i && i < s_prev.len());
                assert(ValidBitString(s_prev));
            } else {
                assert(s.len() == s_prev.len() + 1);
                assert(i == s_prev.len());
                assert((seq![b]).len() == 1);
                assert(s.index(i) == (seq![b]).index(i - s_prev.len()));
                assert((seq![b]).index(0) == b);
                assert(b == '0' || b == '1');
            }
        }
        assert(ValidBitString(s));

        // Prove Str2Int(s) == n
        assert(s.len() == s_prev.len() + 1);
        let last_idx = s.len() as int - 1;
        assert(last_idx == s_prev.len() as int);
        assert(s.subrange(0, last_idx) == s_prev);
        assert(s.index(last_idx) == b);

        let bitval: nat = if b == '1' { 1nat } else { 0nat };
        // Relate bitval to n % 2
        let r = n % 2;
        assert(0 <= r && r < 2);
        assert(r == 0 || r == 1);
        assert(bitval == r);

        assert(Str2Int(s) == 2 * Str2Int(s_prev) + bitval);
        assert(Str2Int(s_prev) == n / 2);
        assert(Str2Int(s) == 2 * (n / 2) + (n % 2));
        assert(n == 2 * (n / 2) + (n % 2));
        assert(Str2Int(s) == n);
    }
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_DivMod_Zeroes(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
{
    let val = Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@);
    proof { lemma_Str2Int_Int2Str(val); }
    let res_vec = Vec::from_seq(Int2Str(val));
    res_vec
}
// </vc-code>

fn main() {}
}