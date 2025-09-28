// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

/* helper modified by LLM (iteration 5): fixed syntax error in forall quantifier by adding ! */
fn is_separator(s: &String, sep: &String) -> (b: bool)
    ensures
        b == (s@ == sep@),
{
    s == sep
}

fn split_single(s: String, sep: String, maxsplit: Option<usize>) -> (result: Vec<String>)
    requires
        sep@ != Seq::<char>::empty(),
    ensures
        let parts = result@;
        forall|j: int| 0 <= j < parts.len() as int ==> !(parts[j]@ == sep@),
        match maxsplit {
            None => true,
            Some(limit) => parts.len() <= limit + 1,
        },
        parts.len() >= 1,
        s@.len() == 0 ==> parts.len() == 1 && parts[0]@.len() == 0,
        s@ == sep@ ==> parts.len() == 2 && parts[0]@.len() == 0 && parts[1]@.len() == 0,
    decreases
        match maxsplit { None => s@.len() as int, Some(n) => n as int },
{
    if s@.len() == 0 {
        let mut v = Vec::new();
        v.push(String::new());
        v
    } else if s@ == sep@ {
        let mut v = Vec::new();
        v.push(String::new());
        v.push(String::new());
        v
    } else {
        match maxsplit {
            Some(0) => {
                let mut v = Vec::new();
                v.push(s);
                v
            }
            Some(max) => {
                let split_index = find_split_index(&s, &sep, 0);
                if split_index == -1 {
                    let mut v = Vec::new();
                    v.push(s);
                    v
                } else {
                    let left = s[0..split_index as usize].to_string();
                    let right = s[(split_index as usize + sep.len())..].to_string();
                    let mut right_parts = split_single(right, sep.clone(), Some(max - 1));
                    let mut result = Vec::new();
                    result.push(left);
                    result.append(&mut right_parts);
                    result
                }
            }
            None => {
                let split_index = find_split_index(&s, &sep, 0);
                if split_index == -1 {
                    let mut v = Vec::new();
                    v.push(s);
                    v
                } else {
                    let left = s[0..split_index as usize].to_string();
                    let right = s[(split_index as usize + sep.len())..].to_string();
                    let mut right_parts = split_single(right, sep.clone(), None);
                    let mut result = Vec::new();
                    result.push(left);
                    result.append(&mut right_parts);
                    result
                }
            }
        }
    }
}

fn find_split_index(s: &String, sep: &String, start: usize) -> (index: i32)
    requires
        sep@.len() > 0,
        start <= s@.len(),
    ensures
        index == -1 || (start <= index as usize && index as usize <= s@.len() - sep@.len()),
{
    let mut i = start;
    while i <= s.len().saturating_sub(sep.len())
        invariant
            i <= s@.len() - sep@.len() + 1,
            forall|j: int| start as int <= j < i as int ==> !(s@.subrange(j as nat, j as nat + sep@.len() as nat) == sep@),
    {
        if is_separator(&s[i..i + sep.len()].to_string(), sep) {
            return i as i32;
        }
        i += 1;
    }
    -1
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
{
/* code modified by LLM (iteration 5): fixed syntax error in forall quantifier by adding ! */
    let mut result = Vec::with_capacity(a.len());
    let mut i = 0;
    while i < a.len()
        invariant
            0 <= i <= a@.len(),
            result@.len() == i,
            forall|k: int| 0 <= k < i ==> {
                let parts = #[trigger] result@[k];
                let original = #[trigger] a@[k];
                forall|j: int| 0 <= j < parts@.len() as int ==> !(parts@[j] == sep@),
                match maxsplit {
                    None => true,
                    Some(limit) => parts@.len() <= limit + 1,
                },
                parts@.len() >= 1,
                (original.len() == 0 ==> parts@.len() == 1 && parts@[0]@.len() == 0),
                (original == sep@ ==> parts@.len() == 2 && parts@[0]@.len() == 0 && parts@[1]@.len() == 0)
            },
        decreases
            a@.len() - i,
    {
        let current_string = a[i].clone();
        let parts = split_single(current_string, sep.clone(), maxsplit);
        result.push(parts);
        i += 1;
    }
    result
}
// </vc-code>


}
fn main() {}