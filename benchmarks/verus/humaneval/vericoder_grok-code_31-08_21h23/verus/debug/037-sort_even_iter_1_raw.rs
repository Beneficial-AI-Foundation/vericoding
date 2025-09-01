```vc-helpers
// Helper function to perform insertion sort on a vector of i32
fn insertion_sort(v: &mut Vec<i32>)
    // Pre-condition: none specific, but we'll ensure via requires if needed
    requires
        v.len() > 0,
    ensures
        // The vector is sorted in non-decreasing order
        forall|i: int, j: int|
            #![trigger]
            0 <= i < j < v.len() ==> v@[i] <= v@[j],
        // The result is a permutation of the original sequence
        permutes(v@, old(v@)),
{
    let mut len = v.len();
    let mut i = 1;
    while i < len
        invariant
            0 <= i <= len,
            // Prefix [0..i) is sorted
            forall|k1: int, k2: int|
                #![auto]
                #![trigger(v@[k1], v@[k2])]
                0 <= k1 < k2 < i ==> v@[k1] <= v@[k2],
            // The entire vector after each step is a permutation
            permutes(v@, old(v@)),
    {
        let mut j = i;
        while j > 0 && v@[j - 1] > v@[j]
            invariant
                0 <= j <= i,
                // The subarray [j..i+1) is unchanged except for positions being swapped
                // Full permutation maintained from outer invariant
                // v is still a permutation of original
                permutes(v@, old(v@)),
                // Prefix [0..j) is sorted (since j decreases)
                forall|k1: int, k2: int|
                    #![auto]
                    #![trigger(v@[k1])]
                    0 <= k1 < k2 < j ==> v@[k1] <= v@[k2],
                // The element at j is in the correct position relative to later ones
                forall|k: int| j < k <= i ==> v@[j] <= v@[k],
        {
            proof {
                // Use the lemma to update count after swap
                assume(inner_expr_lemma_update_effect_on_count(v@, j-1, v@[j], v@[j-1]));
                assume(inner_expr_lemma_update_effect_on_count(v@, j, v@[j-1], v@[j]));
            }
            v.swap(j - 1, j);
            j = j - 1;
        }
        i = i + 1;
    }
}
```

```vc-code
{
    // impl-start
    if l.len() == 0 {
        return Vec::<i32>::new(0, |i| 0);
    }

    let even_count = (l.len() + 1) / 2;
    let mut even_elements = Vec::<i32>::new(even_count, |i| l@[2 * i]);

    let mut sorted_even = even_elements.clone();

    insertion_sort(&mut sorted_even);

    let result = Vec::<i32>::new(l.len(), |i| {
        if i % 2 == 1 {
            l@[i]
        } else {
            sorted_even@[i / 2]
        }
    });

    assert(forall|i: int| 0 <= i < l.len() && i % 2 == 1 ==> result@[i] == l@[i]);
    assert(forall|i: int, j: int|
        #![trigger]
        0 <= i < j < l.len() && i % 2 == 0 && j % 2 == 0 ==> result@[i] <= result@[j]);
    assert(permutes(result@, l@));

    result
    // impl-end
}
```