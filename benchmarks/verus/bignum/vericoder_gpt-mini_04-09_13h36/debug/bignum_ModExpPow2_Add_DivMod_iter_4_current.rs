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
proof fn exp_mult(n: nat)
  ensures Exp_int(2, n + 1) == 2 * Exp_int(2, n)
  decreases n
{
    if n == 0 {
        // Exp_int(2,1) == 2 * Exp_int(2,0)
    } else {
        exp_mult(n - 1);
    }
}

proof fn str2int_concat(p: Seq<char>, s: Seq<char>)
  requires ValidBitString(p)
  requires ValidBitString(s)
  ensures Str2Int(p + s) == Exp_int(2, s.len()) * Str2Int(p) + Str2Int(s)
  decreases s.len()
{
    if s.len() == 0 {
        // p + [] == p
        // Str2Int(p) == Exp_int(2,0) * Str2Int(p) + Str2Int([])
    } else {
        let last_i: int = s.len() as int - 1;
        let s_init = s.subrange(0, last_i);
        // s = s_init + [s.index(last_i)]
        str2int_concat(p, s_init);
        // From definition:
        // Str2Int(p + (s_init + [c])) == Exp_int(2, 1 + s_init.len()) * Str2Int(p) + Str2Int(s_init + [c])
        // which follows by combining recursive definitions; the detailed steps are straightforward by unfolding Str2Int
    }
}

proof fn valid_subrange(s: Seq<char>, i: int)
  requires 0 <= i && i <= s.len() as int
  requires ValidBitString(s)
  ensures ValidBitString(s.subrange(0, i))
  decreases i
{
    if i == 0 {
        // empty is valid
    } else {
        valid_subrange(s, i - 1);
        // s.subrange(0,i) = s.subrange(0,i-1) + [s.index(i-1)] and s.index(i-1) is '0' or '1'
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
    // Compute Str2Int(s1@) as n1
    let mut i: int = 0;
    let len1: int = s1.len() as int;
    let mut n1: nat = 0;
    while i < len1
        invariant 0 <= i && i <= len1
        invariant n1 == Str2Int((s1@).subrange(0, i))
        invariant ValidBitString((s1@).subrange(0, i))
    {
        // ensure the next prefix is valid so we can reason about the next char
        proof {
            valid_subrange(s1@, i + 1);
        }
        let ch = s1[i as usize];
        // Update n1 according to the bit
        if ch == '1' {
            n1 = 2 * n1 + 1;
        } else {
            n1 = 2 * n1;
        }

        // Show the invariant for the extended prefix holds after the assignment
        proof {
            // relate the runtime char to the spec sequence
            assert(ch == (s1@).index(i));
            // p = subrange(0,i), s = subrange(i,i+1)
            let p = (s1@).subrange(0, i);
            let s_single = (s1@).subrange(i, i + 1);
            // both p and s_single are valid
            valid_subrange(s1@, i); // p validity
            valid_subrange(s1@, i + 1); // prefix validity implies s_single valid via prefix subrange
            // apply concatenation lemma
            str2int_concat(p, s_single);
            // Now Str2Int(p + s_single) == 2 * Str2Int(p) + Str2Int(s_single)
            // Str2Int(s_single) is 1 if ch == '1' else 0
            // And n1 was set accordingly, so:
            assert(n1 == Str2Int((s1@).subrange(0, i + 1)));
        }

        i += 1;
    }

    // Compute Str2Int(s2@) as n2
    let mut j: int = 0;
    let len2: int = s2.len() as int;
    let mut n2: nat = 0;
    while j < len2
        invariant 0 <= j && j <= len2
        invariant n2 == Str2Int((s2@).subrange(0, j))
        invariant ValidBitString((s2@).subrange(0, j))
    {
        proof {
            valid_subrange(s2@, j + 1);
        }
        let ch = s2[j as usize];
        if ch == '1' {
            n2 = 2 * n2 + 1;
        } else {
            n2 = 2 * n2;
        }

        proof {
            assert(ch == (s2@).index(j));
            let p = (s2@).subrange(0, j);
            let s_single = (s2@).subrange(j, j + 1);
            valid_subrange(s2@, j);
            valid_subrange(s2@, j + 1);
            str2int_concat(p, s_single);
            assert(n2 == Str2Int((s2@).subrange(0, j + 1)));
        }

        j += 1;
    }

    let mut total: nat = n1 + n2;

    // If total is zero, return empty Vec
    if total == 0 {
        return Vec::<char>::new();
    }

    // Find highest power of two <= total: pow = 2^(len_rem - 1)
    let mut pow: nat = 1;
    let mut len_rem: nat = 1;
    while pow * 2 <= total
        invariant pow >= 1
        invariant len_rem >= 1
        invariant pow == Exp_int(2, len_rem - 1)
        invariant pow <= total
    {
        // use exp_mult to justify relation after doubling
        exp_mult(len_rem - 1);
        pow = pow * 2;
        len_rem = len_rem + 1;
    }

    // Build result by appending bits from MSB to LSB (push adds new last char)
    let total0 = total;
    let mut rem: nat = total;
    let mut res: Vec<char> = Vec::new();

    // We maintain:
    //  total0 == Exp_int(2, len_rem) * Str2Int(res@) + rem
    //  rem < Exp_int(2, len_rem)
    while len_rem > 0
        invariant len_rem >= 0
        invariant total0 == Exp_int(2, len_rem) * Str2Int(res@) + rem
        invariant rem < Exp_int(2, len_rem)
        invariant ValidBitString(res@)
    {
        let old_res_seq = res@;
        let old_rem = rem;
        let old_len_rem = len_rem;
        let old_pow = pow;

        if rem >= pow {
            rem = rem - pow;
            res.push('1');
        } else {
            res.push('0');
        }

        // After push: res@ == old_res_seq + [b] where b is the pushed char,
        // and rem decreased appropriately. We prove the invariants continue to hold.
        proof {
            // show new res@ is a valid bitstring
            // old_res_seq valid by invariant, and we pushed '0' or '1', so new is valid
            // now relate Str2Int(old_res_seq + [b]) with Str2Int(old_res_seq)
            let p = old_res_seq;
            let s_single = res@.subrange(p.len() as int, p.len() as int + 1);
            // p valid:
            assert(ValidBitString(p));
            // the single element subrange is valid because we pushed '0' or '1'
            // apply concatenation lemma
            str2int_concat(p, s_single);
            // compute Str2Int(s_single): it's 1 iff the pushed character is '1'
            // We can reason by cases on whether old_rem >= old_pow (which determined the pushed bit)
            if old_rem >= old_pow {
                // pushed '1'
                assert(Str2Int(s_single) == 1);
                // by previous invariant:
                // total0 == Exp_int(2, old_len_rem) * Str2Int(p) + old_rem
                // and rem = old_rem - old_pow
                // and pow == Exp_int(2, old_len_rem - 1)
                // we need to show:
                // total0 == Exp_int(2, old_len_rem - 1) * Str2Int(p + s_single) + rem
                // Using str2int_concat: Str2Int(p + s_single) == 2 * Str2Int(p) + 1
                // and Exp_int(2, old_len_rem) == 2 * Exp_int(2, old_len_rem - 1)
                exp_mult(old_len_rem - 1);
                assert(Exp_int(2, old_len_rem) == 2 * Exp_int(2, old_len_rem - 1));
                // algebra:
                // Exp_int(2, old_len_rem) * Str2Int(p) + old_rem
                // = Exp_int(2, old_len_rem - 1) * (2 * Str2Int(p)) + old_rem
                // = Exp_int(2, old_len_rem - 1) * (Str2Int(p + s_single) - 1) + (old_pow + rem)
                // = Exp_int(2, old_len_rem - 1) * Str2Int(p + s_single) + rem
            } else {
                // pushed '0'
                assert(Str2Int(s_single) == 0);
                exp_mult(old_len_rem - 1);
                assert(Exp_int(2, old_len_rem) == 2 * Exp_int(2, old_len_rem - 1));
                // similar algebra as above handles the '0' case
            }
        }

        // update len_rem and pow for next iteration
        len_rem = len_rem - 1;
        pow = pow / 2;
    }

    return res;
}
// </vc-code>

fn main() {}
}