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
/* helper modified by LLM (iteration 8): convert nat to MSB-first bit Seq */
spec fn Nat_to_BitSeq(n: nat) -> Seq<char>
    decreases n
{
    if n == 0 { seq!['0'] } else { let prefix = Nat_to_BitSeq(n / 2); prefix + seq![if n % 2 == 1 {'1'} else {'0'}] }
}

/* helper modified by LLM (iteration 8): proof that Str2Int(Nat_to_BitSeq(n)) == n */
proof fn Nat_to_BitSeq_correct(n: nat)
    ensures Str2Int(Nat_to_BitSeq(n)) == n
    decreases n
{
    if n == 0 {
        assert(Str2Int(seq!['0']) == 0nat);
    } else {
        Nat_to_BitSeq_correct(n / 2);
        let prefix = Nat_to_BitSeq(n / 2);
        let last = if n % 2 == 1 {'1'} else {'0'};
        assert(Str2Int(prefix + seq![last]) == 2 * Str2Int(prefix) + (if last == '1' { 1nat } else { 0nat }));
        assert(Str2Int(prefix) == n / 2);
        assert(2 * (n / 2) + (n % 2) == n);
        assert((if last == '1' { 1nat } else { 0nat }) == n % 2);
        assert(Str2Int(prefix + seq![last]) == n);
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
    /* code modified by LLM (iteration 8): compute modular exponent and convert spec Seq to Vec using int indices */
    let res_spec: nat = Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@);
    let out_spec = Nat_to_BitSeq(res_spec);

    let mut out = Vec::<char>::new();
    let len_i: int = out_spec.len() as int;
    let mut i_int: int = 0 as int;

    while i_int < len_i
        invariant
            0 <= i_int,
            i_int <= len_i,
            out@ == out_spec.subrange(0, i_int),
        decreases
            len_i - i_int
    {
        let c: char = out_spec.index(i_int);
        out.push(c);
        i_int = i_int + 1;
    }

    proof {
        Nat_to_BitSeq_correct(res_spec);
        assert(out@ == out_spec);
        assert(Str2Int(out@) == res_spec);
    }

    out
}
// </vc-code>

fn main() {}
}
