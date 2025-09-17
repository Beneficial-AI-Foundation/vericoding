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
/* helper modified by LLM (iteration 7): nat<->bitstring conversion helpers */
spec fn Nat2Str(n: nat) -> Seq<char>
    decreases n
{
    if n == 0 { Seq::empty() } else { let q = n / 2; let b = if n % 2 == 1 { '1' } else { '0' }; Nat2Str(q) + seq![b] }
}
proof fn nat2str_inverse(n: nat)
    ensures Str2Int(Nat2Str(n)) == n
    decreases n
{
    if n == 0 {
        assert(Str2Int(Nat2Str(0)) == 0);
    } else {
        nat2str_inverse(n / 2);
        assert(Str2Int(Nat2Str(n)) == n);
    }
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_DivMod_Mul_Zeroes(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 7): compute result using spec-level Nat2Str and convert to Vec<char> */
    let sres = Nat2Str(Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@));
    let mut out = Vec::<char>::new();
    let mut i: usize = 0usize;
    while i < sres.len() as usize
        invariant
            i <= sres.len() as usize,
        decreases sres.len() as int - i as int
    {
        out.push(sres.index(i as int));
        i += 1usize;
    }

    out
}
// </vc-code>

fn main() {}
}
