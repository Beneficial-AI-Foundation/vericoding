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

// <vc-spec>
exec fn Mul(s1: &[char], s2: &[char]) -> (res: Vec<char>)
  requires ValidBitString(s1@), ValidBitString(s2@)
  ensures ValidBitString(res@), Str2Int(res@) == Str2Int(s1@) * Str2Int(s2@)
// </vc-spec>
// <vc-code>
{
            fn str_to_int(s: &[char]) -> (n: nat)
                requires ValidBitString(s@)
                ensures n == Str2Int(s@)
            {
                let mut n: nat = 0;
                let mut i = 0;
                while i < s.len()
                    invariant 0 <= i <= s.len()
                    invariant n == Str2Int(s@.subrange(0, i as int))
                {
                    let c = s[i];
                    let bit = if c == '1' { 1 } else { 0 };
                    n = 2 * n + bit;
                    i += 1;
                }
                n
            }

            fn int_to_str(n: nat) -> (s: Vec<char>)
                ensures ValidBitString(s@) && Str2Int(s@) == n
            {
                if n == 0 {
                    vec!['0']
                } else {
                    let mut s = Vec::new();
                    let mut num = n;
                    let mut power = 1;
                    while power <= num {
                        power = power * 2;
                    }
                    power = power / 2;
                    while power > 0 {
                        if num >= power {
                            s.push('1');
                            num = num - power;
                        } else {
                            s.push('0');
                        }
                        power = power / 2;
                    }
                    s
                }
            }

            let n1 = str_to_int(s1);
            let n2 = str_to_int(s2);
            let product = n1 * n2;
            int_to_str(product)
        }
// </vc-code>

// <vc-spec>
exec fn ModExpPow2(sx: &[char], sy: &[char], n: int, sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@),
    n >= 0,
    (Str2Int(sy@) == Exp_int(2, n as nat) || Str2Int(sy@) == 0),
    sy@.len() == (n as nat) + 1,
    Str2Int(sz@) > 1
  ensures ValidBitString(res@),
    Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases n
// </vc-spec>
// <vc-code>
{
            fn str_to_int(s: &[char]) -> (n: nat)
                requires ValidBitString(s@)
                ensures n == Str2Int(s@)
            {
                let mut n: nat = 0;
                let mut i = 0;
                while i < s.len()
                    invariant 0 <= i <= s.len()
                    invariant n == Str2Int(s@.subrange(0, i as int))
                {
                    let c = s[i];
                    let bit = if c == '1' { 1 } else { 0 };
                    n = 2 * n + bit;
                    i += 1;
                }
                n
            }

            fn int_to_str(n: nat) -> (s: Vec<char>)
                ensures ValidBitString(s@) && Str2Int(s@) == n
            {
                if n == 0 {
                    vec!['0']
                } else {
                    let mut s = Vec::new();
                    let mut num = n;
                    let mut power = 1;
                    while power <= num {
                        power = power * 2;
                    }
                    power = power / 2;
                    while power > 0 {
                        if num >= power {
                            s.push('1');
                            num = num - power;
                        } else {
                            s.push('0');
                        }
                        power = power / 2;
                    }
                    s
                }
            }

            let x = str_to_int(sx);
            let y = str_to_int(sy);
            let z = str_to_int(sz);

            if y == 0 {
                int_to_str(1)
            } else {
                let mut base = x % z;
                for i in 0..n {
                    base = (base * base) % z;
                }
                int_to_str(base)
            }
        }
// </vc-code>

fn main() {}
}


