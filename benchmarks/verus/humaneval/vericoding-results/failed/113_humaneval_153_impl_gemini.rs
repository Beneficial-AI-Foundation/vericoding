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
fn exec_counts(s: &Vec<char>) -> (counts: (i32, i32))
    ensures
        counts.0 as int == count_upper(s@),
        counts.1 as int == count_lower(s@),
{
    let mut upper_count: i32 = 0;
    let mut lower_count: i32 = 0;
    let mut i: usize = 0;
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            upper_count as int == count_upper(s@.subrange(0, i as int)),
            lower_count as int == count_lower(s@.subrange(0, i as int)),
        decreases s.len() - i
    {
        let c = s[i];
        if 'A' <= c && c <= 'Z' {
            upper_count = upper_count + 1;
        } else if 'a' <= c && c <= 'z' {
            lower_count = lower_count + 1;
        }
        i = i + 1;
    }
    (upper_count, lower_count)
}

fn exec_strength(s: &Vec<char>) -> (ret: i32)
    ensures
        ret as int == strength(s@),
{
    let (upper, lower) = exec_counts(s);
    upper - lower
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
    let mut max_strength_idx: usize = 0;
    let mut i: usize = 1;
    while i < extensions.len()
        invariant
            extensions@.len() > 0,
            0 <= max_strength_idx < extensions.len(),
            1 <= i <= extensions.len(),
            max_strength_idx < i,
            forall|j: int| 0 <= j < i as int ==> strength(extensions@[max_strength_idx as int]@) >= strength(extensions@[j]@),
            forall|j: int| 0 <= j < max_strength_idx as int ==> strength(extensions@[j]@) < strength(extensions@[max_strength_idx as int]@),
        decreases extensions.len() - i
    {
        let current_strength = exec_strength(&extensions[i]);
        let max_strength = exec_strength(&extensions[max_strength_idx]);
        if current_strength > max_strength {
            max_strength_idx = i;
        }
        i = i + 1;
    }

    let mut result = class_name.clone();
    result.push('.');
    
    let mut ext_to_append = extensions[max_strength_idx].clone();
    result.append(&mut ext_to_append);
    
    result
}
// </vc-code>


}

fn main() {}