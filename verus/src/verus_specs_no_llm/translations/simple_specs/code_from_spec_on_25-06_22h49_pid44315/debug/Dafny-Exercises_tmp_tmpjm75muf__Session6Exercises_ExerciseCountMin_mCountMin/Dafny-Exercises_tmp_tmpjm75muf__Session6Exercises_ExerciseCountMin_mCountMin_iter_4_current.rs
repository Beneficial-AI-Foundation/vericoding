use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

// Spec function to find minimum value in a vector
spec fn min(v: Vec<int>, n: int) -> int
    decreases n
{
    if n <= 0 {
        int::MAX
    } else if n == 1 {
        v[0]
    } else {
        let rest_min = min(v, n-1);
        if v[(n-1) as nat] < rest_min { v[(n-1) as nat] } else { rest_min }
    }
}

// Spec function to count occurrences of a value in first n elements
spec fn countMin(v: Vec<int>, val: int, n: int) -> int
    decreases n
{
    if n <= 0 {
        0
    } else {
        let rest_count = countMin(v, val, n-1);
        if v[(n-1) as nat] == val { rest_count + 1 } else { rest_count }
    }
}

// Lemma: minimum of vector with n elements is same as minimum with n-1 elements
// when the nth element is greater than or equal to the minimum of first n-1 elements
proof fn lemma_min_extend(v: Vec<int>, n: int)
    requires
        1 < n <= v.len(),
        v[(n-1) as nat] >= min(v, n-1)
    ensures
        min(v, n) == min(v, n-1)
    decreases n
{
    if n == 2 {
        // Base case: n == 2
        assert(min(v, 1) == v[0]);
        assert(v[1] >= v[0]);
        assert(min(v, 2) == v[0]);
    } else {
        // Recursive case follows from definition
        let rest_min = min(v, n-1);
        assert(v[(n-1) as nat] >= rest_min);
        assert(min(v, n) == rest_min);
    }
}

// Lemma: when we find a new minimum, it becomes the minimum of the extended range
proof fn lemma_new_min(v: Vec<int>, i: nat)
    requires
        0 < i < v.len(),
        v[i] < min(v, i as int)
    ensures
        min(v, (i+1) as int) == v[i]
{
    let rest_min = min(v, i as int);
    assert(v[i] < rest_min);
    // By definition of min, since v[i] < rest_min, min(v, i+1) = v[i]
}

// Helper lemma for proving uniqueness of new minimum
proof fn lemma_all_greater_than_new_min(v: Vec<int>, val: int, k: int)
    requires
        0 < k,
        val < min(v, k)
    ensures
        forall|j: int| 0 <= j < k ==> v[j as nat] > val
    decreases k
{
    if k == 1 {
        assert(min(v, 1) == v[0]);
        assert(val < v[0]);
    } else {
        lemma_all_greater_than_new_min(v, val, k-1);
        assert(forall|j: int| 0 <= j < k-1 ==> v[j as nat] > val);
        let rest_min = min(v, k-1);
        assert(val < min(v, k));
        if v[(k-1) as nat] < rest_min {
            assert(min(v, k) == v[(k-1) as nat]);
            assert(val < v[(k-1) as nat]);
        } else {
            assert(min(v, k) == rest_min);
            assert(val < rest_min);
            assert(v[(k-1) as nat] >= rest_min > val);
        }
    }
}

// Lemma: when we find a new minimum, its count in the extended range is 1
proof fn lemma_new_min_count(v: Vec<int>, i: nat)
    requires
        0 < i < v.len(),
        v[i] < min(v, i as int)
    ensures
        countMin(v, v[i], (i+1) as int) == 1
{
    // First prove all elements before i are greater than v[i]
    lemma_all_greater_than_new_min(v, v[i], i as int);
    
    // Now prove by induction that countMin(v, v[i], i) == 0
    lemma_count_zero_for_absent_value(v, v[i], i as int);
    
    // Finally, countMin(v, v[i], i+1) = countMin(v, v[i], i) + 1 = 0 + 1 = 1
    assert(countMin(v, v[i], (i+1) as int) == countMin(v, v[i], i as int) + 1);
    assert(countMin(v, v[i], (i+1) as int) == 1);
}

// Helper lemma: if a value doesn't appear in first k elements, its count is 0
proof fn lemma_count_zero_for_absent_value(v: Vec<int>, val: int, k: int)
    requires
        forall|j: int| 0 <= j < k ==> v[j as nat] != val
    ensures
        countMin(v, val, k) == 0
    decreases k
{
    if k <= 0 {
        assert(countMin(v, val, k) == 0);
    } else {
        lemma_count_zero_for_absent_value(v, val, k-1);
        assert(v[(k-1) as nat] != val);
        assert(countMin(v, val, k) == countMin(v, val, k-1));
        assert(countMin(v, val, k) == 0);
    }
}

// Lemma: count increases by 1 when we encounter the same minimum
proof fn lemma_same_min_count(v: Vec<int>, val: int, i: nat)
    requires
        0 < i < v.len(),
        val == min(v, i as int),
        v[i] == val
    ensures
        countMin(v, val, (i+1) as int) == countMin(v, val, i as int) + 1
{
    // Follows directly from the definition of countMin
    assert(countMin(v, val, (i+1) as int) == countMin(v, val, i as int) + 1);
}

// Helper lemma: count remains same when element is not equal to target
proof fn lemma_count_unchanged(v: Vec<int>, val: int, i: nat)
    requires
        0 < i < v.len(),
        v[i] != val
    ensures
        countMin(v, val, (i+1) as int) == countMin(v, val, i as int)
{
    // Follows directly from the definition of countMin
}

fn mCountMin(v: Vec<int>) -> (c: int)
    requires
        v.len() > 0
    ensures
        c == countMin(v, min(v, v.len() as int), v.len() as int)
{
    let mut current_min = v[0];
    let mut count = 1;
    let mut i = 1;

    while i < v.len()
        invariant
            0 < i <= v.len(),
            current_min == min(v, i as int),
            count == countMin(v, current_min, i as int),
    {
        if v[i] < current_min {
            // Establish preconditions for lemma_new_min
            assert(v[i] < min(v, i as int));
            
            current_min = v[i];
            count = 1;
            
            // Prove that current_min is now the minimum of first i+1 elements
            lemma_new_min(v, i);
            
            // Prove that count is correct for the new minimum  
            lemma_new_min_count(v, i);
        } else if v[i] == current_min {
            count = count + 1;
            
            // Prove minimum doesn't change
            assert(v[i] >= current_min);
            lemma_min_extend(v, (i+1) as int);
            
            // Count increases by 1
            lemma_same_min_count(v, current_min, i);
        } else {
            // v[i] > current_min, so minimum and count don't change
            assert(v[i] > current_min);
            assert(v[i] >= current_min);
            lemma_min_extend(v, (i+1) as int);
            
            // Count stays the same since v[i] != current_min
            lemma_count_unchanged(v, current_min, i);
        }
        i = i + 1;
    }
    
    count
}

}