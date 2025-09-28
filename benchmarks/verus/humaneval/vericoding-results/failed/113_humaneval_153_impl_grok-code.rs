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
/* helper modified by LLM (iteration 4): renamed exec functions to avoid naming conflicts with spec functions */
fn count_upper_impl(v: &Vec<char>) -> (cnt: usize)
    ensures cnt as int == count_upper(v@)
{
    let mut i: usize = 0;
    let mut cnt: usize = 0;
    while i < v@.len()
    {
        if 'A' <= v@[i] && v@[i] <= 'Z' {
            cnt += 1;
        }
        i += 1;
    }
    cnt
}

/* helper modified by LLM (iteration 4): renamed exec functions to avoid naming conflicts with spec functions */
fn count_lower_impl(v: &Vec<char>) -> (cnt: usize)
    ensures cnt as int == count_lower(v@)
{
    let mut i: usize = 0;
    let mut cnt: usize = 0;
    while i < v@.len()
    {
        if 'a' <= v@[i] && v@[i] <= 'z' {
            cnt += 1;
        }
        i += 1;
    }
    cnt
}

/* helper modified by LLM (iteration 4): renamed exec functions to avoid naming conflicts with spec functions */
fn strength_impl(v: &Vec<char>) -> (res: i64)
    ensures res == count_upper(v@) - count_lower(v@)
{
    (count_upper_impl(v) as i64) - (count_lower_impl(v) as i64)
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
    /* code modified by LLM (iteration 5): fixed compilation error by adjusting invariant formatting to single-line clauses */
    let mut i: usize = 0;
    let mut max_strength = strength_impl(&extensions[0]);
    let mut j: usize = 1;
    while j < extensions.len()
        invariant
            0 <= i as int < extensions@.len(),
            0 <= j as int <= extensions@.len(),
            max_strength as int == strength(extensions@[i]@),
            forall |k: int| 0 <= k < j as int ==> strength(extensions@[k]@) as i64 <= max_strength as i64,
            forall |k: int| 0 <= k < i as int ==> strength(extensions@[k]@) as i64 < max_strength as i64,
        decreases extensions@.len() - (j as int)
    {
        let current_strength = strength_impl(&extensions[j]);
        if current_strength > max_strength {
            i = j;
            max_strength = current_strength;
        }
        j += 1;
    }
    let mut result = class_name.clone();
    result.extend_from_slice(&vec!['.']);
    result.extend_from_slice(&extensions[i]);
    result
}
// </vc-code>


}

fn main() {}