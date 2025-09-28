// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
proof fn lemma_mod_range(x: int, n: int)
    requires
        n > 0,
    ensures
        0 <= x % n < n,
{
    if x >= 0 {
        assert(0 <= x % n < n);
    } else {
        let r = x % n;
        if r < 0 {
            assert(r + n > 0 && r + n < n);
            assert((x % n) + n >= 0 && (x % n) + n < n);
        }
    }
}

proof fn lemma_mod_properties(x: int, n: int)
    requires
        n > 0,
    ensures
        x % n == x - n * (x / n),
{
    assert(x == n * (x / n) + (x % n));
}

proof fn lemma_normalize_index_properties(i: int, shift: int, n: int)
    requires
        n > 0,
    ensures
        0 <= normalize_index(i, shift, n) < n,
        normalize_index(i, shift, n) == (i - shift) % n,
{
    lemma_mod_range(i - shift, n);
    let mod_result = (i - shift) % n;
    if mod_result < 0 {
        assert(normalize_index(i, shift, n) == mod_result + n);
        assert(0 <= mod_result + n < n);
    } else {
        assert(normalize_index(i, shift, n) == mod_result);
    }
}
// </vc-helpers>

// <vc-spec>
spec fn normalize_index(i: int, shift: int, n: int) -> int {
    let src_idx = i - shift;
    let mod_result = src_idx % n;
    if mod_result < 0 { mod_result + n } else { mod_result }
}

fn roll<T>(a: Vec<T>, shift: i32) -> (result: Vec<T>)
    ensures
        result.len() == a.len(),
        a.len() == 0 ==> result@ == a@,
        a.len() > 0 ==> forall|i: int| 0 <= i < a.len() ==> #[trigger] result[i] == a[normalize_index(i, shift as int, a.len() as int)]
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed ghost block syntax and loop structure */
    let n = a.len();
    if n == 0 {
        return a;
    }
    
    let mut result = Vec::new();
    let mut i: usize = 0;
    let ghost_shift = shift as int;
    let ghost_n = n as int;
    
    while i < n
        invariant
            result.len() == i,
            forall|j: int| 0 <= j < i ==> #[trigger] result@[j] == a@[normalize_index(j, ghost_shift, ghost_n)],
    {
        let normalized_idx = normalize_index(i as int, ghost_shift, ghost_n);
        proof {
            lemma_normalize_index_properties(i as int, ghost_shift, ghost_n);
        }
        result.push(a[normalized_idx as usize]);
        i += 1;
    }
    
    result
}
// </vc-code>


}
fn main() {}