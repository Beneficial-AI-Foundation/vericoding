use vstd::prelude::*;

verus! {

// <vc-helpers>
spec fn seq_contains<T>(s: Seq<T>, x: T) -> bool 
    decreases s.len(),
{
    if s.len() == 0 {
        false
    } else {
        s[0] == x || seq_contains(s.subrange(1, s.len() as int), x)
    }
}

spec fn seq_no_duplicates<T>(s: Seq<T>) -> bool 
    decreases s.len(),
{
    if s.len() <= 1 {
        true
    } else {
        !seq_contains(s.subrange(1, s.len() as int), s[0]) && seq_no_duplicates(s.subrange(1, s.len() as int))
    }
}

proof fn seq_contains_iff_exists<T>(s: Seq<T>, x: T)
    ensures
        seq_contains(s, x) <==> exists|i: int| 0 <= i < s.len() && s[i] == x,
    decreases s.len(),
{
    if s.len() == 0 {
    } else {
        seq_contains_iff_exists(s.subrange(1, s.len() as int), x);
    }
}

proof fn seq_no_duplicates_implies_distinct<T>(s: Seq<T>)
    ensures
        seq_no_duplicates(s) ==> forall|i: int, j: int| 0 <= i < j < s.len() ==> s[i] != s[j],
    decreases s.len(),
{
    if s.len() <= 1 {
    } else {
        seq_no_duplicates_implies_distinct(s.subrange(1, s.len() as int));
    }
}

spec fn set_of_seq<T>(s: Seq<T>) -> Set<T> 
    decreases s.len(),
{
    if s.len() == 0 {
        Set::empty()
    } else {
        set_of_seq(s.subrange(1, s.len() as int)).insert(s[0])
    }
}

proof fn set_of_seq_contains_iff<T>(s: Seq<T>, x: T)
    ensures
        set_of_seq(s).contains(x) <==> exists|i: int| 0 <= i < s.len() && s[i] == x,
    decreases s.len(),
{
    if s.len() == 0 {
    } else {
        set_of_seq_contains_iff(s.subrange(1, s.len() as int), x);
    }
}
// </vc-helpers>

// <vc-spec>
fn remove_duplicates(a: &[i32]) -> (result: Vec<i32>)
    ensures
        forall|x: i32| result@.contains(x) <==> exists|i: int| 0 <= i < a.len() && a[i] == x,
        forall|i: int, j: int| 0 <= i < j < result.len() ==> result@[i] != result@[j]
// </vc-spec>
// <vc-code>
{
    let mut result = Vec::new();
    let ghost mut seen: Set<i32> = Set::empty();
    
    let mut idx: usize = 0;
    while idx < a.len()
        invariant
            0 <= idx <= a.len(),
            result@.len() == seen.len(),
            forall|x: i32| seen.contains(x) <==> exists|i: int| 0 <= i < idx && a[i] == x,
            forall|x: i32| result@.contains(x) <==> seen.contains(x),
            seq_no_duplicates(result@),
    {
        let elem = a[idx];
        if !seen.contains(elem) {
            result.push(elem);
            proof {
                seen = seen.insert(elem);
            }
        } else {
            proof {
                seen = seen.insert(elem);
            }
        }
        idx += 1;
    }
    
    result
}
// </vc-code>

fn main() {
}

}