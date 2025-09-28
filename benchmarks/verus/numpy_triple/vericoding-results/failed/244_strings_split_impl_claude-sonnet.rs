// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): wrapped int casts in ghost variables */
fn find_occurrences(s: Seq<char>, sep: Seq<char>) -> (result: Vec<int>)
    requires
        sep.len() > 0,
    ensures
        forall|i: int| 0 <= i < result.len() as int ==> {
            let pos = result[i];
            0 <= pos < s.len() as int &&
            pos + sep.len() as int <= s.len() as int &&
            s.subrange(pos, pos + sep.len() as int) == sep
        },
{
    let mut result = Vec::new();
    let mut i = 0;
    while i + sep.len() <= s.len()
        invariant
            0 <= i <= s.len(),
            forall|j: int| 0 <= j < result.len() as int ==> {
                let pos = result[j];
                0 <= pos < s.len() as int &&
                pos + sep.len() as int <= s.len() as int &&
                s.subrange(pos, pos + sep.len() as int) == sep &&
                pos < i as int
            },
    {
        let ghost i_int = i as int;
        let ghost sep_len_int = sep.len() as int;
        if s.subrange(i_int, i_int + sep_len_int) == sep {
            result.push(i_int);
        }
        i += 1;
    }
    result
}

fn split_string(s: String, sep: String, maxsplit: Option<usize>) -> (result: Vec<String>)
    requires
        sep@ != Seq::<char>::empty(),
    ensures
        result.len() >= 1,
        forall|i: int| 0 <= i < result.len() as int ==> result[i]@ != sep@,
        match maxsplit {
            None => true,
            Some(limit) => result.len() <= limit + 1,
        },
        s@.len() == 0 ==> result.len() == 1 && result[0]@.len() == 0,
        s@ == sep@ ==> result.len() == 2 && result[0]@.len() == 0 && result[1]@.len() == 0,
{
    if s@.len() == 0nat {
        let mut result = Vec::new();
        result.push(String::new());
        return result;
    }
    
    let positions = find_occurrences(s@, sep@);
    let mut result = Vec::new();
    let mut start: int = 0;
    let mut splits_made = 0;
    
    let mut i = 0;
    while i < positions.len()
        invariant
            0 <= i <= positions.len(),
            0 <= start <= s@.len() as int,
            splits_made >= 0,
            result.len() == splits_made,
            match maxsplit {
                None => true,
                Some(limit) => splits_made <= limit,
            },
    {
        if maxsplit.is_some() && splits_made >= maxsplit.unwrap() {
            break;
        }
        
        let pos = positions[i];
        let part = s@.subrange(start, pos);
        result.push(part.into_rust_string());
        let ghost sep_len_int = sep@.len() as int;
        start = pos + sep_len_int;
        splits_made += 1;
        i += 1;
    }
    
    let ghost s_len_int = s@.len() as int;
    let final_part = s@.subrange(start, s_len_int);
    result.push(final_part.into_rust_string());
    result
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
    /* code modified by LLM (iteration 5): simplified main split function implementation */
    let mut result = Vec::new();
    let mut i = 0;
    
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            result.len() == i,
    {
        let parts = split_string(a[i].clone(), sep.clone(), maxsplit);
        result.push(parts);
        i += 1;
    }
    
    result
}
// </vc-code>


}
fn main() {}