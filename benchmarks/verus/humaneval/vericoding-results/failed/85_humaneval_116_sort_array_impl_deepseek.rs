// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn popcount(n: nat) -> nat
    decreases n
{
    if n == 0 { 0 } else { popcount(n / 2) + n % 2 }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fix lemma_popcount_monotonic parameter types and add proper lemma for swap preservation */
proof fn lemma_popcount_monotonic(n: nat, m: nat)
    requires
        n <= m,
    ensures
        popcount(n) <= popcount(m)
    decreases m
{
    if m > n {
        lemma_popcount_monotonic(n, m - 1);
        lemma_popcount_increasing(m - 1, m);
    }
}

proof fn lemma_popcount_increasing(a: nat, b: nat)
    requires
        a < b,
    ensures
        popcount(a) <= popcount(b)
    decreases b
{
    if b > 0 {
        if a > 0 {
            lemma_popcount_increasing(a / 2, b / 2);
        }
        lemma_popcount_mod2(b);
    }
}

spec fn compare_by_popcount(a: u8, b: u8) -> bool {
    popcount(a as nat) <= popcount(b as nat)
}

proof fn lemma_popcount_mod2(n: nat)
    ensures
        popcount(n) == popcount(n / 2) + (n % 2)
    decreases n
{
    if n > 0 {
        lemma_popcount_mod2(n / 2);
    }
}

fn popcount_u8(n: u8) -> (count: u8)
    ensures
        count as nat == popcount(n as nat)
{
    let mut count: u8 = 0;
    let mut x = n;
    
    while x != 0
        invariant
            count as nat + popcount(x as nat) == popcount(n as nat),
            count <= 8,
        decreases x as nat
    {
        count = count + (x & 1);
        x = x >> 1;
    }
    count
}

proof fn lemma_swap_preserves_multiset<T>(v: Vec<T>, i: usize, j: usize)
    requires
        i < v@.len(),
        j < v@.len(),
    ensures
        v@.to_multiset() == v@.update(i, v@[j]).update(j, v@[i])@.to_multiset()
{
}
// </vc-helpers>

// <vc-spec>
fn sort_array(s: Vec<u8>) -> (sorted: Vec<u8>)
    ensures 
        forall|i: int, j: int| 0 <= i < j < sorted@.len() ==> popcount(sorted@[i] as nat) <= popcount(sorted@[j] as nat)
            && sorted@.len() == s@.len()
            && s@.to_multiset() == sorted@.to_multiset()
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fix verification triggers and inner loop invariant */
    let mut sorted = s.clone();
    let mut i: usize = 0;
    
    while i < sorted.len()
        invariant
            i <= sorted@.len(),
            sorted@.len() == s@.len(),
            s@.to_multiset() == sorted@.to_multiset(),
            forall|k: int, l: int| 0 <= k < i <= l < sorted@.len() ==> popcount(sorted@[k] as nat) <= popcount(sorted@[l] as nat),
        decreases sorted.len() - i
    {
        let mut j: usize = i + 1;
        
        while j < sorted.len()
            invariant
                i < j <= sorted@.len(),
                sorted@.len() == s@.len(),
                s@.to_multiset() == sorted@.to_multiset(),
                forall|k: int| #[trigger] i <= k < j ==> popcount(sorted@[k] as nat) <= popcount(sorted@[j - 1] as nat),
            decreases sorted.len() - j
        {
            if popcount_u8(sorted[i]) > popcount_u8(sorted[j]) {
                let temp = sorted[i];
                sorted[i] = sorted[j];
                sorted[j] = temp;
                lemma_swap_preserves_multiset(sorted, i, j);
            }
            j = j + 1;
        }
        i = i + 1;
    }
    sorted
}
// </vc-code>


}

fn main() {}