// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(s: Seq<char>, k: int) -> bool {
    1 <= k <= 26 && 1 <= s.len() <= 1000 && 
    forall|i: int| 0 <= i < s.len() ==> 'a' <= #[trigger] s[i] <= 'z'
}

spec fn unique_chars(s: Seq<char>) -> Set<char> {
    s.to_set()
}

spec fn min_changes(s: Seq<char>, k: int) -> int {
    let unique = unique_chars(s);
    if k <= unique.len() { 0 } else { k - unique.len() }
}

spec fn is_impossible(s: Seq<char>, k: int) -> bool {
    s.len() < k
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): [used usize for array index in exec code] */
fn count_unique_chars(s: &Vec<char>) -> (count: usize)
    requires
        forall|i: int| 0 <= i < s@.len() ==> 'a' <= #[trigger] s@[i] <= 'z',
    ensures
        count as int == unique_chars(s@).len(),
{
    let mut seen = [false; 26];
    let mut count: usize = 0;
    let mut i: usize = 0;
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            forall|j: int| 0 <= j < s@.len() ==> 'a' <= s@[j] <= 'z',
            count as int == s@.subrange(0, i as int).to_set().len(),
            forall|c: char| 'a' <= c <= 'z' ==> (s@.subrange(0, i as int).to_set().contains(c) <==> seen[(c as u8 - 'a' as u8) as int]),
    {
        let c = s[i];
        let index = (c as u8 - 'a' as u8) as usize;

        if !seen[index] {
            seen[index] = true;
            count = count + 1;
        }
        i = i + 1;
    }
    count
}

spec fn nat_to_string_spec(n: nat) -> Seq<char> {
    if n < 10 {
        seq![(n as u8 + '0' as u8) as char]
    } else { // for n < 100
        let d1 = n / 10;
        let d0 = n % 10;
        seq![(d1 as u8 + '0' as u8) as char, (d0 as u8 + '0' as u8) as char]
    }
}

fn int_to_string(n: u64) -> (s: String)
    requires 0 <= n < 100,
    ensures s@ == nat_to_string_spec(n as nat),
{
    let mut res = String::with_capacity(2);
    if n < 10 {
        res.push_char((n as u8 + '0' as u8) as char);
    } else {
        let d1 = n / 10;
        let d0 = n % 10;
        res.push_char((d1 as u8 + '0' as u8) as char);
        res.push_char((d0 as u8 + '0' as u8) as char);
    }
    res
}
// </vc-helpers>

// <vc-spec>
fn solve(s: Vec<char>, k: i8) -> (result: String)
    requires valid_input(s@, k as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): [no changes, resubmitting with helpers fixed] */
    let k_usize = k as usize;

    if s.len() < k_usize {
        proof {
            assert(s@.len() < k as int);
            assert(is_impossible(s@, k as int));
        }
        return "impossible".to_string();
    }

    let unique_count_usize = count_unique_chars(&s);
    let changes_usize = if k_usize <= unique_count_usize { 0 } else { k_usize - unique_count_usize };

    proof {
        // Prove the precondition for int_to_string: 0 <= changes_usize < 100
        let k_int = k as int;
        let unique_count_int = unique_count_usize as int;
        
        // from valid_input spec:
        assert(1 <= k_int <= 26);
        assert(1 <= s@.len());

        // from count_unique_chars ensures:
        assert(unique_count_int == unique_chars(s@).len());

        // A non-empty string of chars has at least one unique char.
        assert(unique_chars(s@).len() >= 1);
        assert(unique_count_int >= 1);

        if k_usize <= unique_count_usize {
            assert(changes_usize == 0);
        } else {
            assert(changes_usize as int == k_int - unique_count_int);
            assert(k_int - unique_count_int <= 26 - 1);
            assert(changes_usize <= 25);
        }
        assert(0 <= changes_usize < 100);
    }
    
    return int_to_string(changes_usize as u64);
}
// </vc-code>


}

fn main() {}