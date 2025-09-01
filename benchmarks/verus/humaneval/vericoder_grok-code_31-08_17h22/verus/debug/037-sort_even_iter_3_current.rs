use vstd::prelude::*;

verus! {

spec fn count<T>(s: Seq<T>, x: T) -> (result:int)
    decreases s.len(),
{
    if s.len() == 0 {
        0
    } else {
        count(s.skip(1), x) + if s[0] == x {
            1int
        } else {
            0int
        }
    }
}
// pure-end
// pure-end

spec fn permutes<T>(s1: Seq<T>, s2: Seq<T>) -> (result:bool) {
    forall|x: T| count(s1, x) == count(s2, x)
}
// pure-end
// pure-end

spec fn inner_expr_lemma_update_effect_on_count<T>(s: Seq<T>, i: int, v: T, x: T) -> (result:bool) {
    count(s.update(i, v), x) == if v == x && s[i] != x {
        count(s, x) + 1
    } else if v != x && s[i] == x {
        count(s, x) - 1
    } else {
        count(s, x)
    }
}
// pure-end

// <vc-helpers>
// Helper functions for managing sequences and sorting
spec fn is_sorted(s: Seq<i32>) -> bool {
    forall|i: int, j: int|
        0 <= i < j < s.len() ==>
        s[i] <= s[j]
}

spec fn is_even(i: int) -> bool {
    i % 2 == 0
}

fn insertion_sort(s: Seq<i32>) -> Seq<i32> 
    requires true
    ensures is_sorted(result), permutes(result, s), result.len() == s.len()  
{
    if s.len() == 0 {
        Seq::empty()
    } else {
        let rest_sorted = insertion_sort(s.take(s.len() - 1));
        insert(rest_sorted, s[s.len() - 1])
    }
}

fn insert(s: Seq<i32>, v: i32) -> Seq<i32> 
    requires is_sorted(s)
    ensures is_sorted(result), result.len() == s.len() + 1, 
           permutes(result, s.push(v))
{
    if s.len() == 0 {
        Seq::new(1, |i| v)
    } else if v <= s[0] {
        Seq::new(s.len() + 1, |i| if i == 0 { v } else { s[i-1]})
    } else {
        s.take(1).concat(insert(s.skip(1), v))
    }
}
// </vc-helpers>

// <vc-spec>
#[verifier::loop_isolation(false)]
fn sort_even(l: Vec<i32>) -> (result: Vec<i32>)
    // post-conditions-start
    ensures
        l.len() == result.len(),
        permutes(result@, l@),
        forall|i: int| 0 <= i < l.len() && i % 2 == 1 ==> result[i] == l[i],
        forall|i: int, j: int|
            #![auto]
            0 <= i < j < l.len() && i % 2 == 0 && j % 2 == 0 ==> result[i] <= result[j],
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    let len = l.len();
    let mut evens: Vec<i32> = Vec::new();
    let mut i = 0;
    while i < len
        invariant
            evens@.len() == (i / 2) + if i % 2 == 0 { 0 } else { 0 },
            forall|k: int| 0 <= k < evens@.len() ==> 
                // unfinished invariant for collecting evens
                exists|idx: int| 
                0 <= idx < i && is_even(idx) && evens@[k] == l@[idx]
    {
        if i % 2 == 0 {
            evens.push_ghost(l@[i]);
            i = i + 1;
        } else {
            i = i + 1;
        }
    } 
    assert(evens@.len() == if len % 2 == 0 { len / 2 } else { len / 2 + 1 });
    
    let sorted_evens = insertion_sort(evens@);
    
    let mut result: Vec<i32> = Vec::new();
    let mut even_idx = 0;
    i = 0;
    while i < len
        invariant
            result@.len() == i,
            even_idx == if i % 2 == 0 { i / 2 } else { (i - 1) / 2 },
            permutes(result@.concat(if even_idx < sorted_evens.len() { sorted_evens.take(even_idx) } else { Seq::empty() }).concat(sorted_evens.skip(even_idx)), l@),
            forall|k: int| 0 <= k < i && is_even(k) ==> result@[k] == sorted_evens[(k / 2)],
            forall|k: int| 0 <= k < i && !is_even(k) ==> result@[k] == l@[k],
    {
        if i % 2 == 0 {
            if even_idx < sorted_evens.len() {
                result.push_ghost(sorted_evens[even_idx]);
            }
            even_idx = even_idx + 1;
        } else {
            result.push_ghost(l@[i]);
        }
        i = i + 1;
    }
    assert(i == len);
    result
}
// </vc-code>

fn main() {}
}