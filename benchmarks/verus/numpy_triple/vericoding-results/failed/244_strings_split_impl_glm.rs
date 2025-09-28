// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): replaced deprecated is_None/is_Some with is_none/is_some */
fn find_next(s: &String, sep: &String, start: usize) -> (pos: Option<usize>)
    requires
        sep.len() > 0,
        start <= s.len(),
    ensures
        pos.is_none() ==> forall|i: int| start as int <= i <= s.len() as int - sep.len() as int ==> s@.subrange(i, i+sep.len() as int) != sep@,
        pos.is_some() ==> {
            let p = pos.unwrap();
            let p_int = p as int;
            let start_int = start as int;
            start_int <= p_int <= s.len() as int - sep.len() as int && s@.subrange(p_int, p_int+sep.len() as int) == sep@
        },
{
    let s_chars: Vec<char> = s.chars().collect();
    let sep_chars: Vec<char> = sep.chars().collect();
    let mut i = start;
    while i <= s_chars.len() - sep_chars.len()
        invariant
            start <= i <= s_chars.len() - sep_chars.len() + 1,
            forall|j: int| start as int <= j < i as int ==> s@.subrange(j, j+sep.len() as int) != sep@,
    {
        let mut j = 0;
        let mut found = true;
        while j < sep_chars.len()
            invariant
                0 <= j <= sep_chars.len(),
                forall|k: int| 0 <= k < j as int ==> s_chars[i + k] == sep_chars[k],
        {
            if s_chars[i + j] != sep_chars[j] {
                found = false;
                break;
            }
            j += 1;
        }
        if found {
            return Some(i);
        }
        i += 1;
    }
    None
}

/* helper modified by LLM (iteration 5): replaced range slicing with loop to avoid exec indexing error */
fn substring(s: &String, start: usize, end: usize) -> (sub: String)
    requires
        start <= end <= s.len(),
    ensures
        sub@ == s@.subrange(start as int, end as int),
{
    let s_chars: Vec<char> = s.chars().collect();
    let mut sub_chars = Vec::new();
    let mut idx = start;
    while idx < end
        invariant
            start <= idx <= end,
            sub_chars@ == s@.subrange(start as int, idx as int),
    {
        sub_chars.push(s_chars[idx]);
        idx += 1;
    }
    String::from_iter(sub_chars)
}

/* helper modified by LLM (iteration 5): replaced deprecated is_Some with is_some */
fn split_single_string(s: String, sep: String, maxsplit: Option<usize>) -> (parts: Vec<String>)
    requires
        sep@ != Seq::<char>::empty(),
    ensures
        parts.len() >= 1,
        forall|j: int| 0 <= j < parts.len() as int ==> #[trigger] parts[j]@ != sep@,
        match maxsplit {
            None => true,
            Some(limit) => parts.len() <= limit + 1,
        },
        (s@.len() == 0 ==> parts.len() == 1 && parts[0]@.len() == 0),
        (s@ == sep@ ==> parts.len() == 2 && parts[0]@.len() == 0 && parts[1]@.len() == 0),
{
    let mut parts: Vec<String> = Vec::new();
    let mut start: usize = 0;
    let mut count: usize = 0;

    while start < s.len() && (maxsplit.is_none() || count < maxsplit.unwrap())
        invariant
            start <= s.len(),
            parts.len() == count,
            forall|j: int| 0 <= j < parts.len() as int ==> parts[j]@ != sep@,
    {
        let found = find_next(&s, &sep, start);
        if found.is_some() {
            let pos = found.unwrap();
            let part = substring(&s, start, pos);
            parts.push(part);
            start = pos + sep.len();
            count += 1;
        } else {
            break;
        }
    }

    let remaining = substring(&s, start, s.len());
    parts.push(remaining);

    parts
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
    /* code modified by LLM (iteration 5): using corrected helper functions */
    let mut result = Vec::new();
    for i in 0..a.len()
        invariant
            result.len() == i,
    {
        let parts = split_single_string(a[i], sep.clone(), maxsplit);
        result.push(parts);
    }
    result
}
// </vc-code>


}
fn main() {}