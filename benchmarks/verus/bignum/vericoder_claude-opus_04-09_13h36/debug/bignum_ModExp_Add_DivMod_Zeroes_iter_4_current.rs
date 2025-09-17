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
exec fn BinaryToNat(s: &[char]) -> (res: nat)
    requires ValidBitString(s@)
    ensures res == Str2Int(s@)
    decreases s@.len()
{
    if s.len() == 0 {
        0nat
    } else {
        let rest = BinaryToNat(&s[..s.len() - 1]);
        let last_digit = if s[s.len() - 1] == '1' { 1nat } else { 0nat };
        proof {
            assert(s@.subrange(0, s@.len() as int - 1) =~= s[..s.len() - 1]@);
        }
        2 * rest + last_digit
    }
}

exec fn NatToBinary(mut n: nat) -> (res: Vec<char>)
    ensures ValidBitString(res@)
    ensures Str2Int(res@) == n
    decreases n
{
    if n == 0 {
        Vec::new()
    } else {
        let mut res = NatToBinary(n / 2);
        if n % 2 == 0 {
            res.push('0');
        } else {
            res.push('1');
        }
        proof {
            assert(res@.len() >= 1);
            let prev = res@.subrange(0, res@.len() as int - 1);
            assert(Str2Int(prev) == n / 2);
            if n % 2 == 0 {
                assert(res@.index(res@.len() as int - 1) == '0');
                assert(Str2Int(res@) == 2 * Str2Int(prev) + 0);
            } else {
                assert(res@.index(res@.len() as int - 1) == '1');
                assert(Str2Int(res@) == 2 * Str2Int(prev) + 1);
            }
            assert(Str2Int(res@) == n);
        }
        res
    }
}

exec fn DecrementBinary(s: &[char]) -> (res: Vec<char>)
    requires ValidBitString(s@)
    requires Str2Int(s@) > 0
    ensures ValidBitString(res@)
    ensures Str2Int(res@) == (Str2Int(s@) - 1) as nat
{
    let n = BinaryToNat(s);
    NatToBinary((n - 1) as nat)
}

exec fn ModuloOp(sa: &[char], sb: &[char]) -> (res: Vec<char>)
    requires ValidBitString(sa@)
    requires ValidBitString(sb@)
    requires Str2Int(sb@) > 0
    ensures ValidBitString(res@)
    ensures Str2Int(res@) == Str2Int(sa@) % Str2Int(sb@)
{
    let a = BinaryToNat(sa);
    let b = BinaryToNat(sb);
    NatToBinary(a % b)
}

exec fn MultiplyMod(sa: &[char], sb: &[char], sm: &[char]) -> (res: Vec<char>)
    requires ValidBitString(sa@)
    requires ValidBitString(sb@)
    requires ValidBitString(sm@)
    requires Str2Int(sm@) > 0
    ensures ValidBitString(res@)
    ensures Str2Int(res@) == (Str2Int(sa@) * Str2Int(sb@)) % Str2Int(sm@)
{
    let a = BinaryToNat(sa);
    let b = BinaryToNat(sb);
    let m = BinaryToNat(sm);
    NatToBinary((a * b) % m)
}

exec fn IsZero(s: &[char]) -> (res: bool)
    requires ValidBitString(s@)
    ensures res == (Str2Int(s@) == 0)
{
    s.len() == 0 || s.iter().all(|&c| c == '0')
}

exec fn OneBinary() -> (res: Vec<char>)
    ensures ValidBitString(res@)
    ensures Str2Int(res@) == 1
{
    let mut res = Vec::new();
    res.push('1');
    proof {
        assert(res@.len() == 1);
        assert(res@.index(0) == '1');
        assert(Str2Int(res@) == 2 * Str2Int(res@.subrange(0, 0)) + 1);
        assert(Str2Int(res@.subrange(0, 0)) == 0);
        assert(Str2Int(res@) == 1);
    }
    res
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_Add_DivMod_Zeroes(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
{
    if IsZero(sy) {
        let one = OneBinary();
        ModuloOp(&one, sz)
    } else {
        let y_minus_1 = DecrementBinary(sy);
        let x_mod = ModuloOp(sx, sz);
        let recursive_result = ModExp_Add_DivMod_Zeroes(&x_mod, &y_minus_1, sz);
        
        proof {
            assert(Str2Int(y_minus_1@) == (Str2Int(sy@) - 1) as nat);
            assert(Str2Int(recursive_result@) == Exp_int(Str2Int(x_mod@), Str2Int(y_minus_1@)) % Str2Int(sz@));
            assert(Str2Int(x_mod@) == Str2Int(sx@) % Str2Int(sz@));
            assert(Exp_int(Str2Int(sx@), Str2Int(sy@)) == Str2Int(sx@) * Exp_int(Str2Int(sx@), (Str2Int(sy@) - 1) as nat));
        }
        
        MultiplyMod(&x_mod, &recursive_result, sz)
    }
}
// </vc-code>

fn main() {}
}