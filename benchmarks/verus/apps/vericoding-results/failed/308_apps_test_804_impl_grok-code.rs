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
fn get_unique(s: &[char]) -> (unique: Set<char>)
    requires
        forall|i: int| 0 <= i < s@.len() ==> 'a' <= #[trigger] s@[i] <= 'z',
    ensures
        unique === unique_chars(s@),
{
    let mut set = Set::empty();
    let mut ii = 0;
    while (ii < s.len())
        invariant
            0 <= ii <= s.len(),
            set === unique_chars(s@.subrange(0, ii as int)),
    {
        set.insert(s[ii]);
        ii += 1;
    }
    set
}
// </vc-helpers>

// <vc-spec>
fn solve(s: Vec<char>, k: i8) -> (result: String)
    requires valid_input(s@, k as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Replaced forbidden len() cast with explicit loop to count unique characters */
    proof {
        assert(valid_input(s@, k as int));
    }
    let k_usize: usize = k as usize;
    let unique_set: Set<char> = get_unique(&s);
    let mut unique_count: usize = 0;
    let mut ch: u8 = b'a';
    while ch <= b'z'
        invariant
            b'a' <= ch <= b'z' + 1,
            unique_count == nat_to_int(unique_set.fin_contains_iter(b'a' as char, ch as char).count),
    {
        if unique_set.contains(ch as char) {
            unique_count += 1;
        }
        ch += 1;
    }
    if s.len() < k_usize {
        return "IMPOSSIBLE".to_string();
    } else if k_usize <= unique_count {
        return s.iter().cloned().collect::<String>();
    } else {
        let missing: usize = k_usize - unique_count;
        let used = unique_set;
        let mut unused: Vec<char> = Vec::new();
        let mut ch: u8 = b'a';
        while unused.len() < missing {
            let c: char = ch as char;
            if !used.contains(c) {
                unused.push(c);
            }
            ch += 1;
        }
        let mut result_s = s.clone();
        for i in 0..missing {
            result_s[i] = unused[i];
        }
        return result_s.iter().cloned().collect::<String>();
    }
}
// </vc-code>


}

fn main() {}