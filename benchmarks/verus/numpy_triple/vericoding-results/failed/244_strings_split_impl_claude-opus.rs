// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fix type mismatches between nat and usize */
fn string_equals(s1: &String, s2: &String) -> (result: bool)
    ensures
        result == (s1@ == s2@),
{
    if s1@.len() != s2@.len() {
        return false;
    }
    let mut i: usize = 0;
    while i < s1@.len() as usize
        invariant
            0 <= i <= s1@.len(),
            s1@.len() == s2@.len(),
            forall|j: int| 0 <= j < i as int ==> s1@[j] == s2@[j],
    {
        if s1.get_char(i) != s2.get_char(i) {
            return false;
        }
        i = i + 1;
    }
    true
}

fn substring_at(s: &String, start: usize, len: usize) -> (result: String)
    requires
        start + len <= s@.len(),
    ensures
        result@ == s@.subrange(start as int, (start + len) as int),
{
    let mut result = String::new();
    let mut i: usize = 0;
    while i < len
        invariant
            0 <= i <= len,
            start + len <= s@.len(),
            result@ == s@.subrange(start as int, (start + i) as int),
    {
        result.push(s.get_char(start + i));
        i = i + 1;
    }
    result
}

fn matches_at(s: &String, pos: usize, pattern: &String) -> (result: bool)
    requires
        pos + pattern@.len() <= s@.len(),
    ensures
        result == (s@.subrange(pos as int, (pos + pattern@.len()) as int) == pattern@),
{
    let substr = substring_at(s, pos, pattern@.len() as usize);
    string_equals(&substr, pattern)
}
// </vc-helpers>

// <vc-spec>
fn split(a: Vec<String>, sep: String, maxsplit: Option<usize>) -> (result: Vec<Vec<String>>)
    requires
        sep@ != Seq::<char>::empty(),
        a.len() > 0,
    ensures
        result.len() == a.len(),
        forall|i: int| 0 <= i < result.len() as int ==> {
            let parts = #[trigger] result[i]@;
            let original = #[trigger] a[i]@;
            (forall|j: int| 0 <= j < parts.len() as int ==> parts[j]@ != sep@) &&
            (match maxsplit {
                None => true,
                Some(limit) => parts.len() <= limit + 1,
            }) &&
            parts.len() >= 1 &&
            (original.len() == 0 ==> parts.len() == 1 && parts[0]@.len() == 0) &&
            (original == sep@ ==> parts.len() == 2 && parts[0]@.len() == 0 && parts[1]@.len() == 0)
        },
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Fix type mismatches between nat and usize */
{
    let mut result: Vec<Vec<String>> = Vec::new();
    let mut i: usize = 0;
    
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            result.len() == i,
            forall|k: int| 0 <= k < i as int ==> {
                let parts = #[trigger] result[k]@;
                let original = #[trigger] a[k]@;
                (forall|j: int| 0 <= j < parts.len() as int ==> parts[j]@ != sep@) &&
                (match maxsplit {
                    None => true,
                    Some(limit) => parts.len() <= limit + 1,
                }) &&
                parts.len() >= 1 &&
                (original.len() == 0 ==> parts.len() == 1 && parts[0]@.len() == 0) &&
                (original == sep@ ==> parts.len() == 2 && parts[0]@.len() == 0 && parts[1]@.len() == 0)
            },
    {
        let s = &a[i];
        let mut parts: Vec<String> = Vec::new();
        
        if s@.len() == 0nat {
            parts.push(String::new());
        } else if string_equals(s, &sep) {
            parts.push(String::new());
            parts.push(String::new());
        } else {
            let mut j: usize = 0;
            let mut split_count: usize = 0;
            let mut last_split: usize = 0;
            
            while j <= s@.len() as usize
                invariant
                    0 <= j <= s@.len(),
                    0 <= last_split <= j,
                    0 <= split_count,
                    parts.len() == split_count,
                    forall|k: int| 0 <= k < parts.len() as int ==> parts[k]@ != sep@,
                    match maxsplit {
                        None => true,
                        Some(limit) => split_count <= limit,
                    },
            {
                if j == s@.len() as usize {
                    let part = substring_at(s, last_split, j - last_split);
                    parts.push(part);
                    j = j + 1;
                } else if j + (sep@.len() as usize) <= s@.len() as usize && matches_at(s, j, &sep) && (maxsplit.is_none() || split_count < maxsplit.unwrap()) {
                    let part = substring_at(s, last_split, j - last_split);
                    parts.push(part);
                    split_count = split_count + 1;
                    j = j + (sep@.len() as usize);
                    last_split = j;
                } else {
                    j = j + 1;
                }
            }
            
            if parts.len() == 0 {
                parts.push(s.clone());
            }
        }
        
        result.push(parts);
        i = i + 1;
    }
    
    result
}
// </vc-code>


}
fn main() {}