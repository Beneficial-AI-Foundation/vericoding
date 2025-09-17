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
proof fn lemma_Exp_step(x: nat, i: nat)
    ensures
        Exp_int(x, i + 1) == x * Exp_int(x, i),
{
}

proof fn lemma_Str2Int_push(s: Seq<char>, c: char)
    requires
        ValidBitString(s.push(c)),
    ensures
        Str2Int(s.push(c)) == 2 * Str2Int(s) + (if c == '1' { 1nat } else { 0nat }),
{
}

proof fn lemma_Str2Int_prefix_step(s: Seq<char>, i: int)
    requires
        ValidBitString(s),
        0 <= i,
        i < s.len() as int,
    ensures
        Str2Int(s.subrange(0, i + 1)) == 2 * Str2Int(s.subrange(0, i)) + (if s.index(i) == '1' { 1nat } else { 0nat }),
{
}

proof fn lemma_div_mod_by_2(n: nat)
    ensures
        2 * (n / 2) + n % 2 == n,
{
}

proof fn lemma_ValidBitString_push_0(s: Seq<char>)
    requires
        ValidBitString(s),
    ensures
        ValidBitString(s.push('0')),
{
}

proof fn lemma_ValidBitString_push_1(s: Seq<char>)
    requires
        ValidBitString(s),
    ensures
        ValidBitString(s.push('1')),
{
}

/* helper modified by LLM (iteration 2): fix nat literals and loop increments */
fn pow(x: nat, y: nat) -> (r: nat)
    ensures
        r == Exp_int(x, y),
{
    let mut acc: nat = 1nat;
    let mut i: nat = 0nat;
    while i < y
        invariant
            i <= y,
            acc == Exp_int(x, i),
        decreases y - i
    {
        acc = acc * x;
        proof { lemma_Exp_step(x, i); }
        i = i + 1nat;
    }
    acc
}

/* helper modified by LLM (iteration 2): use nat literals and correct accumulation */
fn from_bits(s: &[char]) -> (n: nat)
    requires
        ValidBitString(s@),
    ensures
        n == Str2Int(s@),
{
    let mut acc: nat = 0nat;
    let mut i: usize = 0;
    while i < s.len()
        invariant
            0 <= i as int <= s.len() as int,
            ValidBitString(s@),
            acc == Str2Int(s@.subrange(0, i as int)),
        decreases s.len() as int - i as int
    {
        let ch = s[i];
        let bit: nat = if ch == '1' { 1nat } else { 0nat };
        proof { lemma_Str2Int_prefix_step(s@, i as int); }
        acc = 2nat * acc + bit;
        i = i + 1;
    }
    acc
}

/* helper modified by LLM (iteration 2): use nat literals in comparisons and arithmetic */
fn to_bits(n: nat) -> (v: Vec<char>)
    ensures
        ValidBitString(v@),
        Str2Int(v@) == n,
    decreases n
{
    if n == 0nat {
        Vec::<char>::new()
    } else {
        let q: nat = n / 2nat;
        let r: nat = n % 2nat;
        let mut s = to_bits(q);
        let sp = s@;
        if r == 1nat {
            s.push('1');
            proof {
                lemma_ValidBitString_push_1(sp);
                lemma_Str2Int_push(sp, '1');
                assert(q == n / 2nat);
                assert(r == n % 2nat);
                lemma_div_mod_by_2(n);
                assert(2 * q + r == n);
                assert(Str2Int(s@) == 2 * Str2Int(sp) + 1nat);
                assert(Str2Int(sp) == q);
                assert(Str2Int(s@) == n);
            }
        } else {
            s.push('0');
            proof {
                lemma_ValidBitString_push_0(sp);
                lemma_Str2Int_push(sp, '0');
                assert(q == n / 2nat);
                assert(r == n % 2nat);
                lemma_div_mod_by_2(n);
                assert(2 * q + r == n);
                assert(Str2Int(s@) == 2 * Str2Int(sp) + 0nat);
                assert(Str2Int(sp) == q);
                assert(Str2Int(s@) == n);
            }
        }
        s
    }
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_DivMod_ModExpPow2_Mul_Zeroes(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): implement modular exponent using helpers and ensure nat-safe operations */
    let x = from_bits(sx);
    let y = from_bits(sy);
    let z = from_bits(sz);
    let p = pow(x, y);
    let m = p % z;
    let res_vec = to_bits(m);
    res_vec
}
// </vc-code>

fn main() {}
}
