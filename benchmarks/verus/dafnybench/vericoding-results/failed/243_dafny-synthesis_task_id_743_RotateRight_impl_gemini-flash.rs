use vstd::prelude::*;

verus! {

// <vc-helpers>
fn mod_len(a: int, b: int) -> int
    requires b > 0,
    ensures 0 <= mod_len(a, b) < b,
{
    let res = a % b;
    if res < 0 {
        res + b
    } else {
        res
    }
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
    let len_nat: nat = l.len();
    let len: int = len_nat as int;

    if len == 0 {
        return Seq::<int>::new();
    }

    let actual_n: int = n % len; 
    let actual_n_mod = mod_len(actual_n, len);

    let mut result = Seq::<int>::new();
    let mut i: int = 0;

    while i < len
        invariant
            0 <= i <= len,
            result.len() == i,
            forall|j: int| 0 <= j < i ==> 
                result.index(j) == l.index(mod_len(j - actual_n_mod, len)),
    {
        let original_idx = mod_len(i - actual_n_mod, len);
        let val = l.index(original_idx);
        result = result.push(val);
        i = i + 1;
    }

    proof {
        assert forall|idx: int| 0 <= idx < len implies result.index(idx) == l.index(mod_len(idx - n, len)) by {
            assert(actual_n == (n % len));
            assert(mod_len(idx - n, len) == mod_len(idx - n % len, len)); // Added intermediate assertion for clarity
            assert(mod_len(idx - (n % len), len) == mod_len(idx - actual_n, len));
            assert(mod_len(idx - actual_n, len) == mod_len(idx - actual_n_mod, len));
        };
    }

    result
}
// </vc-code>

fn main() {}

}