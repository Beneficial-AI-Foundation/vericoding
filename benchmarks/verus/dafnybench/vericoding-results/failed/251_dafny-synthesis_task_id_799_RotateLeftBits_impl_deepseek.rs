use vstd::prelude::*;

verus! {

// <vc-helpers>
proof fn rotate_left_bits_lemma(n: u32, d: int)
    requires 0 <= d < 32
    ensures ((n << d) | (n >> (32 - d))) as u32 == (((n as nat) << d) | ((n as nat) >> (32 - d))) % 0x1_0000_0000
{
}

proof fn bits32_range_lemma(x: u32)
    ensures 0 <= x as nat < 0x1_0000_0000
{
    assert(0 <= x as nat < 0x1_0000_0000);
}

proof fn shift_mask_lemma(n: u32, d: int)
    requires 0 <= d < 32
    ensures (n << d) as nat == (n as nat) << d
    ensures (n >> (32 - d)) as nat == (n as nat) >> (32 - d)
{
}

proof fn or_lemma(a: u32, b: u32)
    ensures (a | b) as nat == (a as nat) | (b as nat)
{
}

proof fn rotate_left_eq_shift_or(n: u32, d: u32)
    requires 0 <= d < 32
    ensures n.rotate_left(d) == ((n << d) | (n >> (32 - d)))
{
    vstd::pervasive::native::rotate_left_axioms_u32(n, d);
}
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
fn rotate_left_bits(n: u32, d: int) -> (result: u32)
    requires 0 <= d < 32
    ensures result == ((n << d) | (n >> (32 - d)))
// </vc-spec>
// <vc-code>
{
    proof {
        bits32_range_lemma(n);
        shift_mask_lemma(n, d);
        shift_mask_lemma(n, (32 - d) as int);
        or_lemma(n << d, n >> (32 - d));
    }
    
    let result = n.rotate_left(d as u32);
    proof {
        rotate_left_eq_shift_or(n, d as u32);
        assert(result == ((n << d) | (n >> (32 - d))));
    }
    result
}
// </vc-code>

fn main() {
}

}