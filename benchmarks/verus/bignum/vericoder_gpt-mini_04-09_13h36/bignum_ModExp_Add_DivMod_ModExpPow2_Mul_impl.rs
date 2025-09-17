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
exec fn nat_to_bits(n: nat) -> (res: Vec<char>)
  ensures ValidBitString(res@), Str2Int(res@) == n
  decreases n
{
  if n == 0nat {
    Vec::<char>::new()
  } else {
    let mut v = nat_to_bits(n / 2nat);
    let old_seq = v@;
    let b = if n % 2nat == 1nat { '1' } else { '0' };
    v.push(b);
    proof {
      // The new sequence has length one more than the old sequence
      assert(v@.len() as int == old_seq.len() as int + 1);
      // The prefix (all but last) of the new sequence equals the old sequence
      assert(v@.subrange(0, v@.len() as int - 1) == old_seq);
      // By definition of Str2Int, the value of the new sequence equals
      // 2 * value(prefix) + bit(last)
      assert(Str2Int(v@) == 2nat * Str2Int(old_seq) + (if b == '1' { 1nat } else { 0nat }));
      // From the recursive postcondition
      assert(Str2Int(old_seq) == n / 2nat);
      // Arithmetic fact: 2*(n/2) + (n%2) == n
      assert(2nat * (n / 2nat) + (n % 2nat) == n);
      // Conclude the desired equality
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
  nat_to_bits(Str2Int(s1@) + Str2Int(s2@))
}
// </vc-code>

fn main() {}
}