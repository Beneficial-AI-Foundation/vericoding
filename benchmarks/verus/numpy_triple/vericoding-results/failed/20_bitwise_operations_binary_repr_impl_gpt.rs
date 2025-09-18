// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn nat_to_binary_string(n: nat) -> Seq<char>
    decreases n
{
    if n == 0 {
        seq!['0']
    } else {
        let digit = if n % 2 == 0 { '0' } else { '1' };
        nat_to_binary_string(n / 2).push(digit)
    }
}

spec fn is_valid_binary(s: Seq<char>) -> bool {
    s.len() > 0 && (forall|i: int| 0 <= i < s.len() ==> s[i] == '0' || s[i] == '1')
}

spec fn is_valid_signed_binary(s: Seq<char>) -> bool {
    if s.len() > 0 && s[0] == '-' {
        is_valid_binary(s.skip(1))
    } else {
        is_valid_binary(s)
    }
}
// </vc-preamble>

// <vc-helpers>
proof fn lemma_nat_to_binary_is_valid(n: nat) ensures is_valid_binary(nat_to_binary_string(n)) decreases n { if n == 0 { } else { lemma_nat_to_binary_is_valid(n / 2); } }

fn nat_to_binary_vec(n: u64) -> (v: Vec<char>) ensures v@ == nat_to_binary_string(n as nat) decreases n { if n == 0 { let mut v: Vec<char> = Vec::new(); v.push('0'); v } else { let mut v = nat_to_binary_vec(n / 2); let digit = if n % 2 == 0 { '0' } else { '1' }; v.push(digit); v } }
// </vc-helpers>

// <vc-spec>
fn binary_repr(num: i32, width: Option<usize>) -> (result: Vec<char>)
    requires 
        width.is_some() ==> width.get_Some_0() >= 1,
    ensures 

        width.is_none() ==> is_valid_signed_binary(result@),
        width.is_some() ==> is_valid_binary(result@),

        width.is_some() ==> result.len() == width.get_Some_0(),

        (num >= 0 && width.is_none()) ==> 
            result@ == nat_to_binary_string(num as nat),

        (num < 0 && width.is_none()) ==> 
            result@.len() > 0 && result@[0] == '-' && is_valid_binary(result@.skip(1)),

        (num < 0 && width.is_some()) ==> {
            let w = width.get_Some_0();
            let two_comp = (1u32 << w) as i32 + num;
            two_comp >= 0 && two_comp < (1i32 << w) && result.len() == w
        }
// </vc-spec>
// <vc-code>
{
    let result = match width {
        None => {
            if num >= 0 {
                let v = nat_to_binary_vec(num as u64);
                proof { lemma_nat_to_binary_is_valid(num as nat); }
                v
            } else {
                let mut v: Vec<char> = Vec::new();
                v.push('-');
                let n64: i64 = num as i64;
                let abs_u64: u64 = if n64 < 0 { (-n64) as u64 } else { n64 as u64 };
                let tail = nat_to_binary_vec(abs_u64);
                proof { lemma_nat_to_binary_is_valid(abs_u64 as nat); }
                let mut i: usize = 0;
                while i < tail.len()
                    invariant i <= tail.len()
                    invariant v.len() == i + 1
                    invariant v@.len() == (i + 1) as int
                    invariant v@[0] == '-'
                    invariant forall|k: int| 1 <= k < v@.len() ==> v@[k] == '0' || v@[k] == '1'
                    decreases tail.len() - i
                {
                    let c = tail[i];
                    v.push(c);
                    i = i + 1;
                }
                v
            }
        }
        Some(w) => {
            let mut bits: Vec<char> = Vec::new();
            let mut i: usize = 0;
            let mut t: i128 = num as i128;
            while i < w
                invariant i <= w
                invariant bits.len() == i
                invariant forall|k: int| 0 <= k < bits@.len() ==> bits@[k] == '0' || bits@[k] == '1'
                decreases w - i
            {
                let mut r: i128 = t % 2;
                if r < 0 { r = r + 2; }
                let ch = if r == 0 { '0' } else { '1' };
                bits.push(ch);
                t = (t - r) / 2;
                i = i + 1;
            }
            let mut v: Vec<char> = Vec::new();
            let mut j: usize = 0;
            while j < w
                invariant j <= w
                invariant bits.len() == w
                invariant v.len() == j
                invariant forall|k: int| 0 <= k < v@.len() ==> v@[k] == '0' || v@[k] == '1'
                decreases w - j
            {
                let idx = w - 1 - j;
                let c = bits[idx];
                v.push(c);
                j = j + 1;
            }
            v
        }
    };
    result
}
// </vc-code>

}
fn main() {}