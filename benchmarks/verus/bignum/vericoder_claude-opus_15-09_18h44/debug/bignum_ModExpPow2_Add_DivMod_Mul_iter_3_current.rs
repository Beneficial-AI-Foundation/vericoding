
use vstd::prelude::*;

verus! {

spec fn Str2Int(s: Seq<char>) -> nat
  recommends ValidBitString(s)
  decreases s.len()
{
  if s.len() == 0 {
    0
  } else {
    2 * Str2Int(s.subrange(0, s.len() as int - 1))
      + (if s.index(s.len() as int - 1) == '1' { 1nat } else { 0nat })
  }
}

spec fn ValidBitString(s: Seq<char>) -> bool
{
  forall |i: int| 0 <= i && i < s.len() as int ==>
    (s.index(i) == '0' || s.index(i) == '1')
}

// <vc-helpers>
proof fn pow2_positive(n: nat)
    ensures
        pow2(n) > 0
{
    reveal(pow2);
    if n == 0 {
    } else {
        pow2_positive((n - 1) as nat);
    }
}

spec fn pow2(n: nat) -> nat
    decreases n
{
    if n == 0 {
        1
    } else {
        2 * pow2((n - 1) as nat)
    }
}

proof fn str2int_bounds(s: Seq<char>)
    requires
        ValidBitString(s)
    ensures
        Str2Int(s) < pow2(s.len() as nat)
    decreases s.len()
{
    if s.len() == 0 {
    } else {
        str2int_bounds(s.subrange(0, s.len() as int - 1));
        assert(Str2Int(s.subrange(0, s.len() as int - 1)) < pow2((s.len() - 1) as nat));
    }
}

/* helper modified by LLM (iteration 3): Fixed syntax - use spec fn instead of ghost fn */
spec fn ghost_str2int(s: Seq<char>) -> nat
    recommends
        ValidBitString(s)
    decreases s.len()
{
    if s.len() == 0 {
        0
    } else {
        2 * ghost_str2int(s.subrange(0, s.len() as int - 1))
            + (if s.index(s.len() as int - 1) == '1' { 1nat } else { 0nat })
    }
}

exec fn int2str(n: nat, bits: usize) -> (res: Vec<char>)
    ensures
        res@.len() == bits,
        ValidBitString(res@),
        Str2Int(res@) == n % pow2(bits as nat)
    decreases bits
{
    if bits == 0 {
        Vec::new()
    } else {
        let mut v = int2str(n / 2, (bits - 1) as usize);
        if n % 2 == 0 {
            v.push('0');
        } else {
            v.push('1');
        }
        proof {
            assert(v@.len() == bits);
            assert(ValidBitString(v@));
            let prev = v@.subrange(0, (bits - 1) as int);
            assert(prev =~= int2str(n / 2, (bits - 1) as usize)@);
            assert(Str2Int(prev) == (n / 2) % pow2((bits - 1) as nat));
        }
        v
    }
}
// </vc-helpers>

// <vc-spec>
exec fn ModExpPow2_Add_DivMod_Mul(a: &[char], b: &[char]) -> (res: Vec<char>)
  requires ValidBitString(a@), ValidBitString(b@)
  ensures ValidBitString(res@)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): Using spec values directly instead of ghost variables */
    let a_val = Str2Int(a@);
    let b_val = Str2Int(b@);
    
    let max_len = if a.len() > b.len() { a.len() } else { b.len() };
    let result_len = max_len + 1;
    
    proof {
        str2int_bounds(a@);
        str2int_bounds(b@);
        pow2_positive(result_len as nat);
        assert(ghost_str2int(a@) == Str2Int(a@));
        assert(ghost_str2int(b@) == Str2Int(b@));
    }
    
    let sum = (a_val + b_val) % pow2(result_len as nat);
    let res = int2str(sum, result_len);
    
    res
}
// </vc-code>

fn main() {}
}

