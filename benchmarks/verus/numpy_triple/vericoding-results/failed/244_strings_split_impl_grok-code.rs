// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): implemented splitting logic with a while loop to build parts, adding find_first_occurrence helper */
fn find_first_occurrence(s: Seq<char>, sep: Seq<char>) -> Option<usize>
    requires
        sep != Seq::<char>::empty(),
    ensures
        match result {
            Some(i) => 0 <= i <= s.len() - sep.len() && s.subrange(i as int, sep.len() as int) == sep,
            None => !exists|i: int| 0 <= i <= s.len() - sep.len() && s.subrange(i, sep.len() as int) == sep,
        },
{
    let mut i: usize = 0;
    while i <= s.len().checked_sub(sep.len()).unwrap_or(usize::MAX)
        invariant
            (i == 0 || !exists|j: int| 0 <= j < i && s.subrange(j as int, sep.len() as int) == sep),
    {
        if s.subrange(i as int, sep.len() as int) == sep {
            return Some(i);
        }
        i += 1;
    }
    None
}

fn split_single_string(s: Seq<char>, sep: Seq<char>, maxsplit: Option<usize>) -> (result: Vec<String>)
    requires
        sep != Seq::<char>::empty(),
    ensures
        forall|j: int| 0 <= j < result.len() as int ==> result[j]@ != sep,
        match maxsplit {
            None => true,
            Some(limit) => result.len() <= limit + 1,
        },
        result.len() >= 1,
        s.len() == 0 ==> (result.len() == 1 && result[0]@.len() == 0),
        equal(s, sep) ==> (result.len() == 2 && result[0]@.len() == 0 && result[1]@.len() == 0),
{
    let mut result: Vec<String> = Vec::new();
    let mut remaining = s;
    let mut splits_done = 0;
    let limit = match maxsplit {
        Some(l) => l,
        None => usize::MAX,
    };
    while splits_done < limit {
        let pos_opt = find_first_occurrence(remaining, sep);
        match pos_opt {
            Some(pos) => {
                let part = remaining.subrange(0, pos as int);
                result.push(String::from(part));
                remaining = remaining.subrange(pos + sep.len(), remaining.len() - pos - sep.len());
                splits_done += 1;
            }
            None => {
                break;
            }
        }
    }
    result.push(String::from(remaining));
    if result.len() == 0 {
        result.push(String::from(Seq::<char>::empty()));
    }
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
/* code modified by LLM (iteration 3): unchanged as helper fix should resolve issues */
{
    let mut result: Vec<Vec<String>> = Vec::new();
    let mut i: usize = 0;
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            result.len() == i as int,
    {
        let parts = split_single_string(a[i]@, sep@, maxsplit);
        result.push(parts);
        i += 1;
    }
    result
}
// </vc-code>


}
fn main() {}