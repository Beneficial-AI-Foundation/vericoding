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

spec fn permutes<T>(s: Seq<T>, s2: Seq<T>) -> (result:bool) {
    forall|x: T| count(s1, x) == count(s2, x)
}
// pure-end

spec fn is_sorted(s: Seq<i32>) -> bool {
    forall|i: int, j: int| 0 <= i <= j < s.len() ==> s[i] <= s[j]
}

proof fn lemma_update_effect_on_count<T>(s: Seq<T>, i: int, v: T, x: T)
    // pre-conditions-start
    requires
        0 <= i < s.len(),
    // pre-conditions-end
    // post-conditions-start
    ensures
        count(s.update(i, v), x) == if v == x && s[i] != x {
            count(s, x) + 1
        } else if v != x && s[i] == x {
            count(s, x) - 1
        } else {
            count(s, x)
        },
    decreases s.len(),
    // post-conditions-end
{
    // impl-start
    if s.len() == 0 {
        return ;
    }
    if i == 0 {
        assert(s.update(i, v) =~= seq![v] + s.skip(1));
        assert(s.update(i, v).skip(1) =~= s.skip(1));
    } else {
        assert(s.update(i, v) =~= seq![s[0]] + s.skip(1).update(i - 1, v));
        assert(s.update(i, v).skip(1) =~= s.skip(1).update(i - 1, v));
        lemma_update_effect_on_count(s.skip(1), i - 1, v, x);
    }
    // impl-end
}
// pure-end

proof fn lemma_swapping_produces_a_permutation<T>(s: Seq<T>, i: int, j: int)
    // pre-conditions-start
    requires
        0 <= i < s.len(),
        0 <= j < s.len(),
    // pre-conditions-end
    // post-conditions-start
    ensures
        permutes(s.update(i, s[j]).update(j, s[i]), s),
    // post-conditions-end
{
    // impl-start
    assert forall|x: T| #[trigger] count(s.update(i, s[j]).update(j, s[i]), x) == count(s, x) by {
        lemma_update_effect_on_count(s, i, s[j], x);
        lemma_update_effect_on_count(s.update(i, s[j]), j, s[i], x);
    }
    // impl-end
}
// pure-end

/* code modified by LLM (iteration 1): added simple bubble sort implementation with Verus specs */
fn bubble_sort(v: &mut Vec<i32>)
    ensures
        v.len() == old(v).len(),
        is_sorted(v@),
        permutes(v@, old(v)@),
{
    let n = v.len();
    for i in 0..n
        invariant
            v.len() == n,
            forall|k1: int, k2: int| i <= k1 <= k2 < n ==> v[k1] <= v[k2],
            permutes(v@, old(v)@),
    {
        for j in 0..(n - i - 1)
            invariant
                v.len() == n,
                forall|k1: int, k2: int| i <= k1 <= k2 < n ==> v[k1] <= v[k2],
                forall|k: int| n - i <= k < n ==> 
                    forall|l: int| 0 <= l <= j ==> v[l] <= v[k],
                permutes(v@, old(v)@),
        {
            if v[j] > v[j + 1] {
                proof {
                    lemma_swapping_produces_a_permutation(v@, j as int, (j + 1) as int);
                }
                let temp = v[j];
                v.set(j, v[j + 1]);
                v.set(j + 1, temp);
            }
        }
    }
}

fn sort_third(l: Vec<i32>) -> (l_prime: Vec<i32>)
    // post-conditions-start
    ensures
        l_prime.len() == l.len(),
        forall|i: int| 0 <= i < l.len() && i % 3 != 0 ==> l_prime[i] == l[i],
        forall|i: int, j: int|
            0 <= i < j < l.len() && i % 3 == 0 && j % 3 == 0 ==> l_prime[i] <= l_prime[j],
        permutes(l_prime@, l@),
    // post-conditions-end
{
    let mut result = l.clone();
    
    // Extract elements at indices divisible by 3
    let mut third_elements = Vec::new();
    let mut third_indices: Vec<usize> = Vec::new();
    
    for i in 0..result.len()
        invariant
            third_elements.len() == third_indices.len(),
            forall|k: int| 0 <= k < third_indices.len() ==> 
                third_indices[k] < result.len() && third_indices[k] % 3 == 0,
            forall|k: int| 0 <= k < third_elements.len() ==> 
                third_elements[k] == result[third_indices[k] as int],
            forall|k1: int, k2: int| 0 <= k1 < k2 < third_indices.len() ==> 
                third_indices[k1] < third_indices[k2],
    {
        if i % 3 == 0 {
            third_elements.push(result[i]);
            third_indices.push(i);
        }
    }
    
    /* code modified by LLM (iteration 1): replaced standard sort with custom bubble_sort */
    bubble_sort(&mut third_elements);
    
    // Put sorted elements back
    for i in 0..third_indices.len()
        invariant
            result.len() == l.len(),
            third_elements.len() == third_indices.len(),
            is_sorted(third_elements@),
            forall|k: int| 0 <= k < third_indices.len() ==> 
                third_indices[k] < result.len() && third_indices[k] % 3 == 0,
            forall|j: int| 0 <= j < result.len() && j % 3 != 0 ==> result[j] == l[j],
            forall|k1: int, k2: int| 0 <= k1 < k2 < i ==> 
                result[third_indices[k1] as int] <= result[third_indices[k2] as int],
            forall|k1: int, k2: int| 0 <= k1 < i && i <= k2 < third_indices.len() ==> 
                result[third_indices[k1] as int] <= third_elements[k2],
    {
        result.set(third_indices[i], third_elements[i]);
    }
    
    result
}

}
fn main() {}