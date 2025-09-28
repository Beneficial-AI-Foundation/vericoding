// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(n: int, s: Seq<char>) -> bool {
    n == s.len() && n >= 1
}

spec fn count_distinct_chars(s: Seq<char>) -> int {
    s.to_set().len() as int
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): added proper proof steps and fixed subset reasoning */
spec fn count_distinct_in_prefix(s: Seq<char>, end: int) -> int {
    s.subrange(0, end).to_set().len() as int
}

proof fn lemma_distinct_count_monotonic(s: Seq<char>, i: int, j: int)
    requires
        0 <= i <= j <= s.len(),
    ensures
        count_distinct_in_prefix(s, i) <= count_distinct_in_prefix(s, j),
{
    let prefix_i = s.subrange(0, i);
    let prefix_j = s.subrange(0, j);
    proof {
        assert(forall|c: char| prefix_i.contains(c) ==> #[trigger] prefix_j.contains(c));
        assert(prefix_i.to_set().subset_of(prefix_j.to_set()));
    }
}

proof fn lemma_vec_to_spec_distinct(vec: Vec<char>, s: Seq<char>)
    requires
        forall|j: int| 0 <= j < vec.len() ==> s.contains(vec@[j]),
        forall|j1: int, j2: int| 0 <= j1 < j2 < vec.len() ==> vec@[j1] != vec@[j2],
        forall|c: char| s.contains(c) ==> vec@.contains(c),
    ensures
        vec.len() == count_distinct_chars(s),
{
    proof {
        assert(forall|c: char| vec@.to_set().contains(c) <==> s.to_set().contains(c));
        assert(vec@.to_set() =~= s.to_set());
    }
}
// </vc-helpers>

// <vc-spec>
fn solve(n: usize, s: Vec<char>) -> (result: i32)
    requires 
        valid_input(n as int, s@)
    ensures 
        n > 26 ==> result == -1,
        n <= 26 ==> result >= 0 && result < n as i32,
        n <= 26 ==> result == s@.len() as i32 - count_distinct_chars(s@)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed bounds checking and invariant preservation */
    if n > 26 {
        return -1;
    }
    
    let mut distinct_chars: Vec<char> = Vec::new();
    let mut i = 0;
    
    while i < n
        invariant
            i <= n,
            i <= s@.len(),
            distinct_chars.len() <= i,
            distinct_chars.len() <= n,
            forall|j: int| 0 <= j < distinct_chars.len() ==> s@.contains(distinct_chars@[j]),
            forall|j1: int, j2: int| 0 <= j1 < j2 < distinct_chars.len() ==> distinct_chars@[j1] != distinct_chars@[j2],
            0 <= i ==> forall|c: char| s@.subrange(0, i as int).contains(c) ==> distinct_chars@.contains(c),
        decreases n - i
    {
        let current_char = s[i];
        let mut found = false;
        let mut j = 0;
        
        while j < distinct_chars.len()
            invariant
                j <= distinct_chars.len(),
                found ==> exists|k: int| 0 <= k < j && distinct_chars@[k] == current_char,
                !found ==> forall|k: int| 0 <= k < j ==> distinct_chars@[k] != current_char,
            decreases distinct_chars.len() - j
        {
            if distinct_chars[j] == current_char {
                found = true;
                proof {
                    assert(distinct_chars@[j as int] == current_char);
                }
                break;
            }
            j += 1;
        }
        
        if !found {
            proof {
                assert(forall|k: int| 0 <= k < distinct_chars.len() ==> distinct_chars@[k] != current_char);
            }
            distinct_chars.push(current_char);
        }
        
        i += 1;
    }
    
    let distinct_count = distinct_chars.len();
    let result = n as i32 - distinct_count as i32;
    
    proof {
        assert(i == n);
        assert(s@.subrange(0, i as int) =~= s@);
        assert(forall|c: char| s@.contains(c) ==> distinct_chars@.contains(c));
        lemma_vec_to_spec_distinct(distinct_chars, s@);
        assert(distinct_count == count_distinct_chars(s@));
    }
    
    result
}
// </vc-code>


}

fn main() {}