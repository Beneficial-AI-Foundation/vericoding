// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn count_upper(s: Seq<char>) -> int
    decreases s.len()
{
    if s.len() == 0 {
        0int
    } else {
        (if 'A' <= s[0] && s[0] <= 'Z' { 1int } else { 0int }) + count_upper(s.skip(1))
    }
}

spec fn count_lower(s: Seq<char>) -> int
    decreases s.len()
{
    if s.len() == 0 {
        0int
    } else {
        (if 'a' <= s[0] && s[0] <= 'z' { 1int } else { 0int }) + count_lower(s.skip(1))
    }
}

spec fn strength(s: Seq<char>) -> int {
    count_upper(s) - count_lower(s)
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): executable strength computation for Vec<char> */
fn strength_exec(s: Vec<char>) -> int
    decreases s.len()
{
    if s.len() == 0 {
        0
    } else {
        let first = s[0];
        let mut tail: Vec<char> = Vec::new();
        let mut i: usize = 1usize;
        while i < s.len()
            invariant
                i <= s.len(),
                tail.len() == i - 1usize,
            decreases s.len() - i
        {
            tail.push(s[i]);
            i = i + 1usize;
        }
        let head_contrib: int = if 'A' <= first && first <= 'Z' { 1 } else { 0 };
        let head_sub: int = if 'a' <= first && first <= 'z' { 1 } else { 0 };
        head_contrib - head_sub + strength_exec(tail)
    }
}

/* helper modified by LLM (iteration 5): lemma relating spec strength to executable strength_exec */
proof fn strength_exec_spec_equiv(s: Vec<char>)
    ensures
        strength(s@) == strength_exec(s),
    decreases s.len()
{
    if s.len() == 0 {
        assert(strength(s@) == 0);
        assert(strength_exec(s) == 0);
    } else {
        let first = s[0];
        let mut tail: Vec<char> = Vec::new();
        let mut i: usize = 1usize;
        while i < s.len()
            invariant
                i <= s.len(),
                tail.len() == i - 1usize,
            decreases s.len() - i
        {
            tail.push(s[i]);
            i = i + 1usize;
        }
        strength_exec_spec_equiv(tail.clone());
        let delta: int = (if 'A' <= first && first <= 'Z' { 1 } else { 0 }) - (if 'a' <= first && first <= 'z' { 1 } else { 0 });
        assert(strength(s@) == delta + strength(tail@));
        assert(strength_exec(s) == delta + strength_exec(tail.clone()));
        assert(strength_exec(tail.clone()) == strength(tail@));
        assert(strength_exec(s) == strength(s@));
    }
}

// </vc-helpers>

// <vc-spec>
fn strongest_extension(class_name: Vec<char>, extensions: Vec<Vec<char>>) -> (result: Vec<char>)
    requires extensions@.len() > 0
    ensures exists|i: int| 0 <= i < extensions@.len() && 
            result@ == class_name@ + seq!['.'] + extensions@[i]@ &&
            (forall|j: int| 0 <= j < extensions@.len() ==> 
                strength(extensions@[i]@) >= strength(extensions@[j]@)) &&
            (forall|j: int| 0 <= j < i ==> 
                strength(extensions@[j]@) < strength(extensions@[i]@))
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): find best extension using executable strength_exec and build result */
    let n: usize = extensions.len();
    let mut best: usize = 0usize;
    let mut i: usize = 1usize;
    while i < n
        invariant
            best < n,
            i <= n,
        decreases n - i
    {
        if strength_exec(extensions[i].clone()) > strength_exec(extensions[best].clone()) {
            best = i;
        }
        i = i + 1usize;
    }
    let mut result = class_name.clone();
    result.push('.');
    let ext_ref = extensions[best].clone();
    let mut k: usize = 0usize;
    while k < ext_ref.len()
        invariant
            k <= ext_ref.len(),
            result.len() == class_name.len() + 1 + k,
        decreases ext_ref.len() - k
    {
        result.push(ext_ref[k]);
        k = k + 1usize;
    }
    result
}

// </vc-code>


}

fn main() {}