// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn filter_chars(s: Seq<char>, c: Seq<char>) -> Seq<char>
    decreases s.len()
{
    if s.len() == 0 {
        Seq::empty()
    } else if c.contains(s[0]) {
        filter_chars(s.subrange(1, s.len() as int), c)
    } else {
        seq![s[0]].add(filter_chars(s.subrange(1, s.len() as int), c))
    }
}

spec fn reverse_seq(s: Seq<char>) -> Seq<char>
    decreases s.len()
{
    if s.len() == 0 {
        Seq::empty()
    } else {
        reverse_seq(s.subrange(1, s.len() as int)).add(seq![s[0]])
    }
}
// </vc-preamble>

// <vc-helpers>
fn contains_exec(v: &Vec<char>, item: char) -> (res: bool)
    ensures
        res == (exists|i: int| 0 <= i < v@.len() && v@[i] == item),
{
    let mut idx = 0;
    while idx < v.len()
        invariant
            0 <= idx <= v@.len(),
            forall|j: int| 0 <= j < idx ==> v@[j] != item,
        decreases v@.len() - idx
    {
        if v[idx] == item {
            return true;
        }
        idx += 1;
    }
    false
}

/* helper modified by LLM (iteration 4): added guard for empty vector, adjusted invariance with auto triggers, and simplified loop to avoid breaks while maintaining weakens invariants */
fn is_palindrome(v: &Vec<char>) -> (res: bool)
    ensures
        res == (v@ == reverse_seq(v@)),
{
    let n = v.len();
    let mut left = 0;
    let mut right = n.checked_sub(1).unwrap_or(0);
    if n == 0 {
        return true;
    }
    let mut res = true;
    while left < right
        invariant
            0 <= left <= right <= n - 1,
            res ==> forall|j: int| #![auto] 0 <= j < left ==> v@[j] == v@[n - 1 - j],
            !res ==> exists|j: int| #![auto] 0 <= j < left && v@[j] != v@[n - 1 - j],
        decreases right - left
    {
        if v[left] != v[right] {
            res = false;
        }
        left += 1;
        right -= 1;
    }
    res
}
// </vc-helpers>

// <vc-spec>
fn reverse_delete(s: Vec<char>, c: Vec<char>) -> (result: (Vec<char>, bool))
    ensures
        result.0@ == filter_chars(s@, c@),
        result.1 == (result.0@ == reverse_seq(result.0@)),
        result.0@.len() <= s@.len(),
        forall|i: int| #![auto] 0 <= i < result.0@.len() ==> !c@.contains(result.0@[i]),
        forall|i: int| #![auto] 0 <= i < result.0@.len() ==> s@.contains(result.0@[i]),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): fixed type annotation for seq![] */
{
    let mut result_vec = Vec::new();
    let mut i = 0;
    while i < s.len()
        invariant
            0 <= i <= s@.len(),
            result_vec@ == filter_chars(s@.subrange(0, i as int), c@),
            forall|k: int| #![auto] 0 <= k < result_vec@.len() ==> !c@.contains(result_vec@[k]) && s@.contains(result_vec@[k]),
        decreases s@.len() - i
    {
        if !contains_exec(&c, s[i]) {
            result_vec.push(s[i]);
            proof {
                assert(filter_chars(s@.subrange(0, (i + 1) as int), c@) ==
                      filter_chars(s@.subrange(0, i as int), c@).add(filter_chars(s@.subrange(i as int, (i + 1) as int), c@)));
                assert(s@.subrange(0, (i + 1) as int).len() == (i + 1) as int);
                assert(s@.subrange(i as int, (i + 1) as int) == seq![s@[i as int]]);
                assert(c@.contains(s@[i as int]) == false);
                assert(filter_chars(seq![s@[i as int]], c@) == seq![s@[i as int]]);
            }
        } else {
            proof {
                assert(c@.contains(s@[i as int]));
                assert(filter_chars(s@.subrange(i as int, (i + 1) as int), c@) == seq![]::<char>);
            }
        }
        i += 1;
    }
    let is_pal = is_palindrome(&result_vec);
    (result_vec, is_pal)
}
// </vc-code>


}

fn main() {}