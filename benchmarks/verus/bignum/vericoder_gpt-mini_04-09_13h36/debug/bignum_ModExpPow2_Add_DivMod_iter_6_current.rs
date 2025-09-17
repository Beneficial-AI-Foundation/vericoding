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
        // unfold definition
        assert(Exp_int(2, 1) == 2 * Exp_int(2, 0));
    } else {
        exp_mult(n - 1);
        // Use the induction hypothesis to show the step for n
        assert(Exp_int(2, n + 1) == 2 * Exp_int(2, n));
    }
}

proof fn valid_subrange(s: Seq<char>, i: nat)
  requires i <= s.len() as nat
  requires ValidBitString(s)
  ensures ValidBitString(s.subrange(0, i as int))
  decreases i
{
    if i == 0 {
        // empty subrange is valid
    } else {
        valid_subrange(s, i - 1);
        assert({
            forall |j: int|
                0 <= j && j < i as int
                ==> (s.subrange(0, i as int).index(j) == '0' || s.subrange(0, i as int).index(j) == '1')
        });
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
    let mut i: nat = 0;
    let len1: nat = s1.len() as nat;
    let mut n1: nat = 0;
    while i < len1
        invariant i <= len1
        invariant n1 == Str2Int((s1@).subrange(0, i as int))
        invariant ValidBitString((s1@).subrange(0, i as int))
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
            assert(ch == (s1@).index(i as int));
            // previous and new prefixes
            let prev = (s1@).subrange(0, i as int);
            let next = (s1@).subrange(0, (i + 1) as int);
            // by definition of Str2Int on a non-empty sequence:
            assert(Str2Int(next) == 2 * Str2Int(prev) + (if (s1@).index(i as int) == '1' { 1 } else { 0 }));
            // n1 was updated accordingly, so it equals Str2Int(next)
            assert(n1 == Str2Int(next));
            // validity of next prefix
            valid_subrange(s1@, i + 1);
        }

        i = i + 1;
    }

    // Compute Str2Int(s2@) as n2
    let mut j: nat = 0;
    let len2: nat = s2.len() as nat;
    let mut n2: nat = 0;
    while j < len2
        invariant j <= len2
        invariant n2 == Str2Int((s2@).subrange(0, j as int))
        invariant ValidBitString((s2@).subrange(0, j as int))
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
            assert(ch == (s2@).index(j as int));
            let prev = (s2@).subrange(0, j as int);
            let next = (s2@).subrange(0, (j + 1) as int);
            assert(Str2Int(next) == 2 * Str2Int(prev) + (if (s2@).index(j as int) == '1' { 1 } else { 0 }));
            assert(n2 == Str2Int(next));
            valid_subrange(s2@, j + 1);
        }

        j = j + 1;
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
            // new sequence is valid because old was valid and we pushed '0' or '1'
            assert(ValidBitString(old_res_seq));
            // establish Str2Int of the appended single-element subsequence
            let p = old_res_seq;
            let b_seq = res@.subrange(p.len() as int, p.len() as int + 1);

            if old_rem >= old_pow {
                // pushed '1'
                assert(Str2Int(b_seq) == 1);
                // use relation pow == Exp_int(2, old_len_rem - 1)
                assert(old_pow == Exp_int(2, old_len_rem - 1));
                // relate Exp_int doubling
                exp_mult(old_len_rem - 1);
                assert(Exp_int(2, old_len_rem) == 2 * Exp_int(2, old_len_rem - 1));
                assert(Exp_int(2, old_len_rem - 1) * (2 * Str2Int(p) + 1) + (old_rem - old_pow)
                       == Exp_int(2, old_len_rem) * Str2Int(p) + old_rem);
                assert(Str2Int(p + b_seq) == 2 * Str2Int(p) + Str2Int(b_seq));
                assert(Exp_int(2, old_len_rem - 1) * Str2Int(p + b_seq) + rem == total0);
            } else {
                // pushed '0'
                assert(Str2Int(b_seq) == 0);
                exp_mult(old_len_rem - 1);
                assert(Exp_int(2, old_len_rem) == 2 * Exp_int(2, old_len_rem - 1));
                assert(Exp_int(2, old_len_rem - 1) * (2 * Str2Int(p)) + old_rem
                       == Exp_int(2, old_len_rem) * Str2Int(p) + old_rem);
                assert(Str2Int(p + b_seq) == 2 * Str2Int(p) + Str2Int(b_seq));
                assert(Exp_int(2, old_len_rem - 1) * Str2Int(p + b_seq) + rem == total0);
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