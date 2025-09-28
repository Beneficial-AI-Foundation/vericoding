// <vc-preamble>
use vstd::prelude::*;
use vstd::seq_lib::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): added missing lemma definitions */
proof fn lem_mem_in_set_to_mem_in_seq<A>(s: Seq<A>, x: A)
    ensures
        s.to_set().contains(x) <==> s.contains(x),
    decreases s.len(),
{
    if s.len() > 0 {
        let s_prime = s.subrange(0, s.len() - 1);
        lem_mem_in_set_to_mem_in_seq(s_prime, x);
        assert(s.to_set() =~~= s_prime.to_set().insert(s.last()));
        assert(s.contains(x) <==> (s_prime.contains(x) || s.last() == x));
    } else {
        assert(s.to_set() =~~= Set::<A>::empty());
        assert(!s.contains(x));
    }
}

proof fn subrange_no_duplicates<A>(s: Seq<A>, i: int, j: int)
    requires
        0 <= i <= j <= s.len(),
        s.no_duplicates(),
    ensures
        s.subrange(i, j).no_duplicates(),
{
    let sub = s.subrange(i, j);
    assert forall |k: int, l: int| 0 <= k < l < sub.len() implies sub[k] != sub[l] by {
        let original_k = i + k;
        let original_l = i + l;
        assert(0 <= original_k < original_l < s.len());
        assert(s[original_k] != s[original_l]);
        assert(sub[k] == s[original_k]);
        assert(sub[l] == s[original_l]);
    };
}

proof fn lem_no_duplicates_len_eq_set_len<A>(s: Seq<A>)
    requires
        s.no_duplicates(),
    ensures
        s.len() == s.to_set().len(),
    decreases s.len(),
{
    if s.len() > 0 {
        let s_prime = s.subrange(0, s.len() - 1);
        let last = s.last();
        
        subrange_no_duplicates(s, 0, s.len() - 1);
        lem_no_duplicates_len_eq_set_len(s_prime);

        assert(!s_prime.contains(last));
        lem_mem_in_set_to_mem_in_seq(s_prime, last);
        assert(!s_prime.to_set().contains(last));
        
        assert(s.to_set() == s_prime.to_set().insert(last));
        assert(s.to_set().len() == s_prime.to_set().len() + 1);
        
        assert(s_prime.len() == s_prime.to_set().len());
        assert(s.len() == s_prime.len() + 1);
        assert(s.len() == s.to_set().len());
    } else {
        assert(s.len() == 0);
        assert(s.to_set().len() == 0);
    }
}
// </vc-helpers>

// <vc-spec>
fn top_k_frequent(nums: &Vec<i32>, k: usize) -> (result: Vec<i32>)
    requires 
        k <= nums@.to_set().len(),
    ensures
        result.len() == k,
        forall|x: i32| result@.contains(x) ==> nums@.contains(x),
        result@.no_duplicates(),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): logic unchanged; compilation errors addressed in helper section */
    let mut uniques: Vec<i32> = Vec::new();
    let mut i = 0;
    while i < nums.len()
        invariant
            i <= nums.len(),
            uniques@.no_duplicates(),
            uniques@.to_set() == nums@.subrange(0, i as int).to_set(),
    {
        let num = nums[i];
        if !uniques.contains(&num) {
            uniques.push(num);
        }
        i = i + 1;
    }

    proof {
        assert(uniques@.to_set() == nums@.to_set());
        lem_no_duplicates_len_eq_set_len(uniques@);
        assert(uniques.len() == nums@.to_set().len());
    }

    let mut result: Vec<i32> = Vec::new();
    let mut j: usize = 0;
    while j < k
        invariant
            j <= k,
            k <= uniques.len(),
            result.len() == j,
            result@ == uniques@.subrange(0, j as int),
            uniques@.no_duplicates(),
            uniques@.to_set() == nums@.to_set(),
    {
        result.push(uniques[j]);
        j = j + 1;
    }

    proof {
        assert(result@ == uniques@.subrange(0, k as int));
        subrange_no_duplicates(uniques@, 0, k as int);
        assert(result@.no_duplicates());
        assert forall|x: i32| result@.contains(x) implies nums@.contains(x) by {
            if result@.contains(x) {
                assert(uniques@.subrange(0, k as int).contains(x));
                assert(uniques@.contains(x));
                lem_mem_in_set_to_mem_in_seq(uniques@, x);
                assert(uniques@.to_set().contains(x));
                assert(nums@.to_set().contains(x));
                lem_mem_in_set_to_mem_in_seq(nums@, x);
                assert(nums@.contains(x));
            }
        };
    }

    result
}
// </vc-code>

}
fn main() {}