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
exec fn nat_to_vec(n: nat) -> (res: Vec<char>)
  ensures ValidBitString(res@), Str2Int(res@) == n
  decreases n
{
    if n == 0 {
        let v: Vec<char> = Vec::new();
        // empty sequence corresponds to 0
        proof {
            assert(Str2Int(v@) == 0);
            assert(ValidBitString(v@));
        }
        v
    } else {
        let q = n / 2;
        let r = n % 2;
        let mut v = nat_to_vec(q);
        // capture old sequence before push
        let old_seq: Seq<char> = v@;
        let c: char = if r == 1 { '1' } else { '0' };
        v.push(c);
        // runtime facts about vector lengths
        assert(v.len() == old_seq.len() + 1);
        proof {
            // work completely in proof mode where nat/int are allowed
            let last_idx: int = (v@.len() as int) - 1;
            assert(v@.index(last_idx) == c);
            // unfold Str2Int for the non-empty sequence v@
            assert(Str2Int(v@) == 2 * Str2Int(v@.subrange(0, last_idx)) + (if v@.index(last_idx) == '1' { 1 } else { 0 }));
            // the subrange equals old_seq
            assert(v@.subrange(0, last_idx) == old_seq);
            assert(Str2Int(v@) == 2 * Str2Int(old_seq) + (if c == '1' { 1 } else { 0 }));
            assert(Str2Int(v@) == 2 * q + r);
            assert(Str2Int(v@) == n);
            assert(ValidBitString(v@));
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
  let res: Vec<char> = nat_to_vec(a + b);
  proof {
      assert(Str2Int(res@) == a + b);
      assert(ValidBitString(res@));
  }
  res
}
// </vc-code>

fn main() {}
}