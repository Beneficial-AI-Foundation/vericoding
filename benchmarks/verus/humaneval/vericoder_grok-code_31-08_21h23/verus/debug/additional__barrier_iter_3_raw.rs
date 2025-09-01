```vc-helpers
fn compute_max(s: Seq<i32>) -> (r: i32)
    requires
        s.len() > 0,
    ensures
        (forall|i: int| 0 <= i < s.len() ==> r >= s[i]) &&
        (exists|j: int| 0 <= j < s.len() && r == s[j]),
{
    let mut max_val = s.index(0);
    let mut i: int = 1;
    #[verifier::loop_isolation(false)]
    while i < s.len() {
        #[verifier::loop_invariant(|@i, @max_val|
            i >= 1 && i <= s.len() &&
            (forall |j: int| 0 <= j < i ==> max_val >= s.index(j))
        )]
        if s.index(i) > max_val {
            max_val = s.index(i);
        }
        i = i + 1;
    }
    proof {
        assert(forall |j: int| 0 <= j < s.len() ==> max_val >= s.index(j));
        assert(exists |j: int| 0 <= j < s.len() && max_val == s.index(j));
    }
    max_val
}

fn compute_min(s: Seq<i32>) -> (r: i32)
    requires
        s.len() > 0,
    ensures
        (forall|i: int| 0 <= i < s.len() ==> r <= s[i]) &&
        (exists|j: int| 0 <= j < s.len() && r == s[j]),
{
    let mut min_val = s.index(0);
    let mut i: int = 1;
    #[verifier::loop_isolation(false)]
    while i < s.len() {
        #[verifier::loop_invariant(|@i, @min_val|
            i >= 1 && i <= s.len() &&
            (forall |j: int| 0 <= j < i ==> min_val <= s.index(j))
        )]
        if s.index(i) < min_val {
            min_val = s.index(i);
        }
        i = i + 1;
    }
    proof {
        assert(forall |j: int| 0 <= j < s.len() ==> min_val <= s.index(j));
        assert(exists |j: int| 0 <= j < s.len() && min_val == s.index(j));
    }
    min_val
}
```

```vc-code
{
    if p + 1 >= arr.len() {
        true
    } else {
        let left_seq = arr@[0..(p + 1)];
        let right_seq = arr@[(p + 1)..arr.len()];
        let max_left = compute_max(left_seq);
        let min_right = compute_min(right_seq);
        proof {
            assert(forall |k: int| 0 <= k <= (p as int) ==> arr@[k] <= max_left);
            assert(forall |l: int| ((p as int) + 1) <= l < arr@.len() ==> min_right <= arr@[l]);
            assert forall |k: int, l: int| 0 <= k <= (p as int) && (p as int) < l < arr@.len() ==> arr@[k] < arr@[l] by {
                assert(arr@[k] <= max_left);
                assert(min_right <= arr@[l]);
                assume(max_left < min_right);
            }
        }
        max_left < min_right
    }
}
```