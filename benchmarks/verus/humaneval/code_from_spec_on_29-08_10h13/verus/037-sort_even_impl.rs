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
proof fn lemma_update_effect_on_count<T>(s: Seq<T>, i: int, v: T, x: T)
    requires 0 <= i < s.len()
    ensures inner_expr_lemma_update_effect_on_count(s, i, v, x)
    decreases s.len()
{
    if s.len() == 1 {
        assert(s.update(i, v) == seq![v]);
        assert(count(s.update(i, v), x) == if v == x { 1int } else { 0int });
        assert(count(s, x) == if s[0] == x { 1int } else { 0int });
    } else {
        if i == 0 {
            assert(s.update(i, v) == seq![v] + s.skip(1));
            assert(count(s.update(i, v), x) == count(s.skip(1), x) + if v == x { 1int } else { 0int });
            assert(count(s, x) == count(s.skip(1), x) + if s[0] == x { 1int } else { 0int });
        } else {
            lemma_update_effect_on_count(s.skip(1), i - 1, v, x);
            assert(s.update(i, v) == seq![s[0]] + s.skip(1).update(i - 1, v));
            assert(count(s.update(i, v), x) == count(s.skip(1).update(i - 1, v), x) + if s[0] == x { 1int } else { 0int });
        }
    }
}

proof fn lemma_permutes_after_even_sort<T>(original: Seq<T>, result: Seq<T>, even_elements: Seq<T>)
    requires 
        original.len() == result.len(),
        forall|i: int| 0 <= i < original.len() && i % 2 == 1 ==> result[i] == original[i],
        forall|i: int, j: int| 0 <= i < original.len() && 0 <= j < even_elements.len() && i % 2 == 0 && i / 2 == j ==> 
            result[i] == even_elements[j],
        even_elements.len() == (original.len() + 1) / 2,
        forall|i: int| 0 <= i < even_elements.len() ==> even_elements[i] == original[2 * i],
    ensures permutes(original, result)
{
    assert forall|x: T| count(original, x) == count(result, x) by {
        let x = choose|x: T| true;
        
        let even_count_orig = count_at_even_positions(original, x, 0);
        let odd_count_orig = count_at_odd_positions(original, x, 0);
        let even_count_res = count_at_even_positions(result, x, 0);
        let odd_count_res = count_at_odd_positions(result, x, 0);
        
        assert(count(original, x) == even_count_orig + odd_count_orig);
        assert(count(result, x) == even_count_res + odd_count_res);
        assert(odd_count_orig == odd_count_res);
        assert(even_count_orig == count(even_elements, x));
        assert(even_count_res == count(even_elements, x));
        assert(count(original, x) == count(result, x));
    }
}

spec fn count_at_even_positions<T>(s: Seq<T>, x: T, start_idx: int) -> int
    decreases s.len() - start_idx
{
    if start_idx >= s.len() {
        0int
    } else if start_idx % 2 == 0 {
        (if s[start_idx] == x { 1int } else { 0int }) + count_at_even_positions(s, x, start_idx + 1)
    } else {
        count_at_even_positions(s, x, start_idx + 1)
    }
}

spec fn count_at_odd_positions<T>(s: Seq<T>, x: T, start_idx: int) -> int
    decreases s.len() - start_idx
{
    if start_idx >= s.len() {
        0int
    } else if start_idx % 2 == 1 {
        (if s[start_idx] == x { 1int } else { 0int }) + count_at_odd_positions(s, x, start_idx + 1)
    } else {
        count_at_odd_positions(s, x, start_idx + 1)
    }
}
// </vc-helpers>

// <vc-description>
/*
function_signature: "def sort_even(l: list)"
docstring: |
This function takes a list l and returns a list l' such that
l' is identical to l in the odd indicies, while its values at the even indicies are equal
to the values of the even indicies of l, but sorted.
test_cases:
- input: [1, 2, 3]
output: [1, 2, 3]
- input: [5, 6, 3, 4]
output: [3, 6, 5, 4]
*/
// </vc-description>

// <vc-spec>
fn sort_even<T: PartialEq + Ord + Copy + vstd::prelude::SpecOrd>(l: Vec<T>) -> (result: Vec<T>)
    ensures 
        result.len() == l.len(),
        forall|i: int| 0 <= i < l.len() && i % 2 == 1 ==> result@[i] == l@[i],
        forall|i: int, j: int| 0 <= i < l.len() && 0 <= j < l.len() && i % 2 == 0 && j % 2 == 0 && i < j ==> 
            result@[i] <= result@[j],
        permutes(l@, result@)
// </vc-spec>

// <vc-code>
{
    let mut even_elements = Vec::new();
    let mut i = 0;
    
    while i < l.len()
        invariant
            0 <= i <= l.len(),
            even_elements.len() == i / 2,
            forall|j: int| 0 <= j < even_elements.len() ==> even_elements@[j] == l@[2 * j]
    {
        if i % 2 == 0 {
            even_elements.push(l[i]);
        }
        i += 1;
    }
    
    /* code modified by LLM (iteration 5): sort the even elements */
    even_elements.sort();
    
    let mut result = l.clone();
    let mut j = 0;
    let mut k = 0;
    
    while j < result.len()
        invariant
            0 <= j <= result.len(),
            0 <= k <= even_elements.len(),
            k == j / 2,
            result.len() == l.len(),
            forall|idx: int| 0 <= idx < j && idx % 2 == 1 ==> result@[idx] == l@[idx],
            forall|idx: int| 0 <= idx < j && idx % 2 == 0 ==> result@[idx] == even_elements@[idx / 2],
            forall|idx: int| j <= idx < result.len() ==> result@[idx] == l@[idx],
            even_elements.len() == (l.len() + 1) / 2,
            forall|idx: int| 0 <= idx < even_elements.len() ==> even_elements@[idx] == l@[2 * idx],
            /* code modified by LLM (iteration 5): add sortedness invariant for even_elements */
            forall|m: int, n: int| 0 <= m <= n < even_elements.len() ==> even_elements@[m] <= even_elements@[n]
    {
        if j % 2 == 0 {
            result.set(j, even_elements[k]);
            k += 1;
        }
        j += 1;
    }
    
    proof {
        lemma_permutes_after_even_sort(l@, result@, even_elements@);
    }
    
    result
}
// </vc-code>

}
fn main() {}