use vstd::prelude::*;

verus! {

/* 
MIPS 0
We implement the following with bitvectors in Verus.
here s' and t' are converted to decimal scalars
s = [1,1,1], t = [1,0,1], ys = [1, 0, 0], s' = 7, t' = 5, ys' = 4
ys' % 2 ^ (len(s)) = (s' + t') % 2 ^ (len(s))
4 % 8 = 12 % 8

def f(s,t):
    a = 0;b = 0;
    ys = []
    for i in range(10):
        c = s[i]; d = t[i];
        next_a = b ^ c ^ d
        next_b = b+c+d>1
        a = next_a;b = next_b;
        y = a
        ys.append(y)
    return ys
*/

spec fn array_to_bv10(arr: Seq<bool>) -> int
    recommends arr.len() == 10
{
    array_to_bv10_helper(arr, 9)
}

spec fn array_to_bv10_helper(arr: Seq<bool>, index: int) -> int
    recommends 0 <= index < arr.len()
    decreases index
{
    if index <= 0 {
        if arr[0] { 1 } else { 0 }
    } else {
        let bit: int = if arr[index] { 1 } else { 0 };
        bit * pow2(index) + array_to_bv10_helper(arr, index - 1)
    }
}

spec fn pow2(n: int) -> int
    recommends n >= 0
    decreases n
{
    if n <= 0 { 1 } else { 2 * pow2(n - 1) }
}

spec fn is_bit_set(x: int, bit_index: int) -> bool
    recommends 0 <= bit_index < 10 && x >= 0
{
    (x / pow2(bit_index)) % 2 == 1
}

spec fn bv10_to_seq(x: int) -> Seq<bool> {
    seq![is_bit_set(x, 0), is_bit_set(x, 1), is_bit_set(x, 2), is_bit_set(x, 3),
         is_bit_set(x, 4), is_bit_set(x, 5), is_bit_set(x, 6), is_bit_set(x, 7),
         is_bit_set(x, 8), is_bit_set(x, 9)]
}

spec fn bool_to_int(a: bool) -> int {
    if a { 1 } else { 0 }
}

spec fn xor_bool(a: bool, b: bool) -> bool {
    (a || b) && !(a && b)
}

spec fn bit_addition(s: Seq<bool>, t: Seq<bool>) -> Seq<bool> 
    recommends s.len() == 10 && t.len() == 10
{
    let a: int = array_to_bv10(s);
    let b: int = array_to_bv10(t);
    let c: int = (a + b) % pow2(10);
    bv10_to_seq(c)
}

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn array_to_sequence(arr: &[bool; 10]) -> (res: Vec<bool>)
    ensures 
        res.len() == 10,
        forall|k: int| 0 <= k < 10 ==> res[k] == arr[k]
// </vc-spec>
// <vc-code>
{
    let mut v: Vec<bool> = Vec::new();
    let mut i: usize = 0;
    while i < 10usize
        invariant
            v.len() == i,
            0 <= i as int && i as int <= 10,
            forall|j: int| 0 <= j && j < i as int ==> #[trigger] v@[j] == arr@[j]
        decreases 10 - i as int
    {
        assert(i < 10usize);
        let val = arr[i];
        let ghost vprev = v@;
        let ghost io: int = i as int;
        v.push(val);
        assert(v@ == vprev.push(val));
        // New length equals i + 1
        assert(v.len() == (io + 1) as usize);
        // The newly added element matches arr at index i
        assert(v@[io] == val);
        assert(arr@[io] == val);
        i = i + 1;
        // Re-establish the quantified invariant up to new i
        assert(forall|j: int| 0 <= j && j < i as int ==> #[trigger] v@[j] == arr@[j]) by {
            assert(forall|j: int| 0 <= j && j < io ==> #[trigger] vprev.push(val)[j] == vprev[j]);
            assert(v@[io] == arr@[io]);
        }
    }
    v
}
// </vc-code>

fn main() {
}

}