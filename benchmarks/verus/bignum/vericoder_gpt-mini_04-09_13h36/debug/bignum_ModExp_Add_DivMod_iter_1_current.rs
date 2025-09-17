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
exec fn nat_to_vec(n: nat) -> Vec<char>
  decreases n
  ensures ValidBitString(result@)
  ensures Str2Int(result@) == n
{
    if n == 0 {
        Vec::new()
    } else {
        let q = n / 2;
        let r = n % 2;
        let mut v = nat_to_vec(q);
        // capture old sequence before push
        let old_seq = v@;
        // we know by induction
        assert(Str2Int(old_seq) == q);
        let c: char = if r == 1 { '1' } else { '0' };
        v.push(c);
        proof {
            // after push, the new vector's sequence has length old_len + 1 and last element c
            assert(v@.len() as int == old_seq.len() as int + 1);
            assert(v@.index(v@.len() as int - 1) == c);
            // unfold Str2Int for the non-empty sequence v@
            assert(Str2Int(v@) == 2 * Str2Int(v@.subrange(0, v@.len() as int - 1)) + (if v@.index(v@.len() as int - 1) == '1' { 1 } else { 0 }));
            // the subrange equals old_seq
            assert(v@.subrange(0, v@.len() as int - 1) == old_seq);
            assert(Str2Int(v@) == 2 * Str2Int(old_seq) + (if c == '1' { 1 } else { 0 }));
            assert(Str2Int(v@) == 2 * q + r);
            assert(Str2Int(v@) == n);
        }
        v
    }
}
// </vc-helpers>

// <vc-spec>
exec fn Add(s1: &[char], s2: &[char]) -> (res: Vec<char>)
  requires ValidBitString(s1@), ValidBitString(s2@)
  ensures ValidBitString(res@), Str2Int(res@) == Str2Int(s1@) + Str2Int(s2@)
// </vc-spec>
// <vc-code>
{
  let a = Str2Int(s1@);
  let b = Str2Int(s2@);
  let res = nat_to_vec(a + b);
  res
}
// </vc-code>

fn main() {}
}