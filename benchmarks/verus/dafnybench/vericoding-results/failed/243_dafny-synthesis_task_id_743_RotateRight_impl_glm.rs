use vstd::prelude::*;

verus! {

// <vc-helpers>
proof fn lemma_mod_equivalence(n: int, len: int, i: int)
    requires len > 0,
    ensures (i - n + len) % len == (i - (n % len)) % len
{
    let k = n % len;
    assert((i - n) % len == (i - k) % len);
    assert((i - n + len) % len == (i - n) % len);
}

proof fn lemma_mod_negative(x: int, len: int)
    requires len > 0,
    requires -len < x < 0,
    ensures (x % len) == x + len
{
    assert(x % len == x + len);
}

proof fn lemma_mod_nonnegative(x: int, len: int)
    requires len > 0,
    requires 0 <= x < len,
    ensures (x % len) == x
{
    assert(x % len == x);
}
// </vc-helpers>

// <vc-spec>
fn rotate_right(l: Seq<int>, n: int) -> (r: Seq<int>)
    requires n >= 0,
    ensures 
        r.len() == l.len(),
        forall|i: int| 0 <= i < l.len() ==> r.index(i) == l.index((i - n + l.len() as int) % l.len() as int),
// </vc-spec>
// <vc-code>
{
    let len_usize = l.len();
    if len_usize == 0 {
        Seq::empty()
    } else {
        let len_int = len_usize as int;
        let k = n % len_int;

        let start1 = (len_int - k) as nat;
        let r = l.subrange(start1, len_usize) + l.subrange(0, start1);
        proof {
            assert forall |i: int| 0 <= i < len_int implies r@[i] == l@[(i - n + len_int) % len_int] by {
                lemma_mod_equivalence(n, len_int, i);
                let j = (i - n + len_int) % len_int;
                let x = i - k;
                if x < 0 {
                    lemma_mod_negative(x, len_int);
                    assert(j == x + len_int);
                    assert(r@[i] == l@[len_int - k + i]);
                    assert(len_int - k + i == x + len_int);
                } else {
                    lemma_mod_nonnegative(x, len_int);
                    assert(j == x);
                    assert(r@[i] == l@[i - k]);
                    assert(i - k == x);
                }
            }
        }
        r
    }
}
// </vc-code>

fn main() {}

}