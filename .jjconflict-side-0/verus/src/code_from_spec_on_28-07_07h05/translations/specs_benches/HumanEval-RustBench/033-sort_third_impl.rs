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

spec fn permutes<T>(s1: Seq<T>, s2: Seq<T>) -> (result:bool) {
    forall|x: T| count(s1, x) == count(s2, x)
}
// pure-end

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

/* code modified by LLM (iteration 2): Added custom sorting function to replace unsupported Rust sort() */
spec fn is_sorted(s: Seq<i32>) -> bool {
    forall|i: int, j: int| 0 <= i < j < s.len() ==> s[i] <= s[j]
}

/* code modified by LLM (iteration 2): Fixed old() syntax for mutable references */
proof fn lemma_swap_preserves_permutation(v: &mut Vec<i32>, i: usize, j: usize, old_v: Seq<i32>)
    requires
        0 <= i < old_v.len(),
        0 <= j < old_v.len(),
        old(v)@ == old_v,
    ensures
        permutes(v@.update(i as int, old_v[j as int]).update(j as int, old_v[i as int]), old_v),
{
    lemma_swapping_produces_a_permutation(old_v, i as int, j as int);
}

fn bubble_sort(v: &mut Vec<i32>)
    ensures
        v.len() == old(v).len(),
        is_sorted(v@),
        permutes(v@, old(v)@),
{
    let n = v.len();
    if n <= 1 {
        return;
    }
    
    let mut i = 0;
    while i < n
        invariant
            0 <= i <= n,
            v.len() == n,
            forall|k: int, l: int| 0 <= k < l < i ==> v[k] <= v[l],
            forall|k: int, l: int| 0 <= k < i && i <= l < n ==> v[k] <= v[l],
            permutes(v@, old(v)@),
    {
        let mut j = 0;
        while j < n - 1 - i
            invariant
                0 <= i < n,
                0 <= j <= n - 1 - i,
                v.len() == n,
                forall|k: int| 0 <= k < n - 1 - i - j ==> 
                    forall|l: int| n - 1 - i - j <= l < n ==> v[k] <= v[l],
                forall|k: int, l: int| 0 <= k < l < i ==> v[k] <= v[l],
                forall|k: int, l: int| 0 <= k < i && i <= l < n ==> v[k] <= v[l],
                permutes(v@, old(v)@),
        {
            if v[j] > v[j + 1] {
                let old_seq = v@;
                /* code modified by LLM (iteration 2): Fixed type mismatch by converting j+1 to usize */
                proof { lemma_swap_preserves_permutation(v, j, (j + 1) as usize, old_seq); }
                let temp = v[j];
                v.set(j, v[j + 1]);
                v.set(j + 1, temp);
            }
            j += 1;
        }
        i += 1;
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
    
    // Extract elements at positions divisible by 3
    let mut third_elements = Vec::new();
    let mut i = 0;
    while i < result.len()
        invariant
            0 <= i <= result.len(),
            third_elements.len() == (i / 3) as nat,
            forall|k: int| 0 <= k < third_elements.len() ==> third_elements[k] == result[k * 3],
    {
        if i % 3 == 0 {
            third_elements.push(result[i]);
        }
        i += 1;
    }
    
    /* code modified by LLM (iteration 2): Replaced unsupported sort() with custom bubble_sort */
    // Sort the extracted elements
    bubble_sort(&mut third_elements);
    
    // Put sorted elements back at positions divisible by 3
    let mut j = 0;
    let mut k = 0;
    while j < result.len()
        invariant
            0 <= j <= result.len(),
            0 <= k <= third_elements.len(),
            k == (j / 3) as nat,
            forall|idx: int| 0 <= idx < j && idx % 3 != 0 ==> result[idx] == l[idx],
            forall|idx: int| 0 <= idx < j && idx % 3 == 0 ==> result[idx] == third_elements[idx / 3],
            forall|idx: int, idy: int| 0 <= idx < idy < j && idx % 3 == 0 && idy % 3 == 0 ==> result[idx] <= result[idy],
            is_sorted(third_elements@),
    {
        if j % 3 == 0 {
            result.set(j, third_elements[k]);
            k += 1;
        }
        j += 1;
    }
    
    result
}

}
fn main() {}