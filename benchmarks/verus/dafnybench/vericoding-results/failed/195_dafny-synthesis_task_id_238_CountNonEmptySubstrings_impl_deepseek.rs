use vstd::prelude::*;

verus! {

// <vc-helpers>
proof fn lemma_triangular_number(n: nat)
    ensures
        (n * (n + 1)) / 2 >= 0,
        (n * (n + 1)) % 2 == 0,
    decreases n,
{
    if n > 0 {
        lemma_triangular_number((n - 1) as nat);
    }
}

proof fn lemma_sum_formula(n: nat)
    ensures
        (n * (n + 1)) / 2 == (n * (n + 1)) / 2,
{
}

spec fn triangular_number(n: nat) -> nat
    recommends n >= 0
{
    (n * (n + 1)) / 2
}

proof fn lemma_nat_to_usize_conversion(n: nat)
    ensures
        n as usize >= 0,
{
}
// </vc-helpers>

// <vc-spec>
fn count_non_empty_substrings(s: Seq<char>) -> (count: usize)
    ensures 
        count >= 0,
        count == (s.len() * (s.len() + 1)) / 2, // Formula for the number of non-empty substrings of a string
// </vc-spec>
// <vc-code>
{
    let mut count: usize = 0;
    let n: usize = s.len();
    
    proof {
        lemma_triangular_number(n as nat);
        lemma_sum_formula(n as nat);
        lemma_nat_to_usize_conversion(n as nat);
    }
    
    let mut i: usize = 0;
    while i < n
        invariant
            0 <= i <= n,
            count as nat == ((i as nat) * ((i as nat) + 1)) / 2,
            ((i as nat) * ((i as nat) + 1)) % 2 == 0,
        decreases n - i,
    {
        count += n - i;
        i += 1;
        
        proof {
            assert(count as nat == (((i - 1) as nat) * (i as nat)) / 2 + ((n - (i - 1)) as nat)) by {
                assert((n - (i - 1)) == (n - i + 1));
            };
            assert((i as nat) * ((i as nat) + 1) / 2 == (((i - 1) as nat) * (i as nat)) / 2 + (i as nat));
        }
    }
    
    assert(count as nat == (n as nat * (n as nat + 1)) / 2) by {
        assert(i == n);
    };
    
    count
}
// </vc-code>

fn main() {
}

}