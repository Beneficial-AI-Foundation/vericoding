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
        seq!['0']
    } else if n % 2 == 1 {
        Int2Str((n - 1) as nat / 2) + seq!['1']
    } else {
        Int2Str(n / 2) + seq!['0']
    }
}

/* helper modified by LLM (iteration 2): implemented proof for correctness of Int2Str */
proof fn Int2StrLemma(n: nat)
    ensures
        ValidBitString(Int2Str(n)),
        Str2Int(Int2Str(n)) == n
    decreases n
{
    if n == 0 {
    } else {
        if n % 2 == 1 {
            let s = Int2Str((n - 1) as nat / 2);
            Int2StrLemma((n - 1) as nat / 2);
            let s1 = s + seq!['1'];
            proof {
                assert(forall |i: int| 0 <= i < s.len() as int ==> (s.index(i) == '0' || s.index(i) == '1'));
                assert(s1.index(s1.len() as int - 1) == '1');
                assert(forall |i: int| 0 <= i < s1.len() as int ==> (s1.index(i) == '0' || s1.index(i) == '1'));
                assert(Str2Int(s1) == 2 * Str2Int(s) + 1);
                assert(Str2Int(s) == ((n - 1) as nat / 2));
                assert(2 * ((n - 1) as nat / 2) + 1 == n);
            }
        } else {
            let s = Int2Str(n / 2);
            Int2StrLemma(n / 2);
            let s1 = s + seq!['0'];
            proof {
                assert(forall |i: int| 0 <= i < s.len() as int ==> (s.index(i) == '0' || s.index(i) == '1'));
                assert(s1.index(s1.len() as int - 1) == '0');
                assert(forall |i: int| 0 <= i < s1.len() as int ==> (s1.index(i) == '0' || s1.index(i) == '1'));
                assert(Str2Int(s1) == 2 * Str2Int(s));
                assert(Str2Int(s) == n / 2);
                assert(2 * (n / 2) == n);
            }
        }
    }
}

/* helper modified by LLM (iteration 2): fixed syntax in signature and confirmed as exec fn */
fn ModExp(x: nat, y: nat, m: nat) -> nat
    requires
        m > 1
    ensures
        res == Exp_int(x, y) % m
    decreases y
{
    if y == 0 {
        1
    } else if y % 2 == 0 {
        let half = ModExp(x, y / 2, m);
        (half * half) % m
    } else {
        let rest = ModExp(x, (y - 1) as nat, m);
        (x * rest) % m
    }
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_DivMod_Mul(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): implemented the modular exponentiation computation and binary conversion to Vec */
    let x = Str2Int(sx@);
    let y = Str2Int(sy@);
    let m = Str2Int(sz@);
    let result_nat = ModExp(x, y, m);
    let mut vec = Vec::with_capacity(1);
    let mut n = result_nat;
    if n == 0 {
        vec.push('0');
    } else {
        while n > 0
            invariant
                n >= 0
        {
            if n % 2 == 1 {
                vec.push('1');
            } else {
                vec.push('0');
            }
            n = n / 2;
        }
        vec.reverse();
    }
    vec
}
// </vc-code>

fn main() {}
}
