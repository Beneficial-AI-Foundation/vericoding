use builtin::*;
use builtin_macros::*;

verus! {

spec fn verifyNeg(a: Vec<int>, n: nat) -> nat
    requires n <= a.len()
    decreases n
{
    if n == 0 {
        0
    } else if a[n - 1] < 0 {
        1 + verifyNeg(a, n - 1)
    } else {
        verifyNeg(a, n - 1)
    }
}

// Helper spec function that counts negatives from start to end (exclusive)
spec fn count_neg_range(a: Vec<int>, start: nat, end: nat) -> nat
    requires start <= end <= a.len()
    decreases end - start
{
    if start == end {
        0
    } else if a[start] < 0 {
        1 + count_neg_range(a, start + 1, end)
    } else {
        count_neg_range(a, start + 1, end)
    }
}

// Helper lemma for splitting ranges
proof fn lemma_count_range_split(a: Vec<int>, start: nat, mid: nat, end: nat)
    requires start <= mid <= end <= a.len()
    ensures count_neg_range(a, start, end) == count_neg_range(a, start, mid) + count_neg_range(a, mid, end)
    decreases mid - start
{
    if start == mid {
        // Base case: count_neg_range(a, start, mid) == 0
        assert(count_neg_range(a, start, mid) == 0);
        assert(count_neg_range(a, start, end) == count_neg_range(a, mid, end));
    } else {
        // Inductive step
        lemma_count_range_split(a, start + 1, mid, end);
        // The recursive call establishes:
        // count_neg_range(a, start + 1, end) == count_neg_range(a, start + 1, mid) + count_neg_range(a, mid, end)
        
        if a[start] < 0 {
            assert(count_neg_range(a, start, end) == 1 + count_neg_range(a, start + 1, end));
            assert(count_neg_range(a, start, mid) == 1 + count_neg_range(a, start + 1, mid));
        } else {
            assert(count_neg_range(a, start, end) == count_neg_range(a, start + 1, end));
            assert(count_neg_range(a, start, mid) == count_neg_range(a, start + 1, mid));
        }
    }
}

// Lemma to prove equivalence between the two counting methods
proof fn lemma_count_equivalence(a: Vec<int>, n: nat)
    requires n <= a.len()
    ensures verifyNeg(a, n) == count_neg_range(a, 0, n)
    decreases n
{
    if n == 0 {
        // Base case: both functions return 0
        assert(verifyNeg(a, 0) == 0);
        assert(count_neg_range(a, 0, 0) == 0);
    } else {
        // Inductive step: assume verifyNeg(a, n-1) == count_neg_range(a, 0, n-1)
        lemma_count_equivalence(a, n - 1);
        
        // Now we need to show verifyNeg(a, n) == count_neg_range(a, 0, n)
        // We know that count_neg_range(a, 0, n) == count_neg_range(a, 0, n-1) + count_neg_range(a, n-1, n)
        lemma_count_range_split(a, 0, n - 1, n);
        
        // count_neg_range(a, n-1, n) is either 0 or 1 depending on a[n-1]
        if a[n - 1] < 0 {
            assert(count_neg_range(a, n - 1, n) == 1);
            assert(verifyNeg(a, n) == 1 + verifyNeg(a, n - 1));
            assert(count_neg_range(a, 0, n) == count_neg_range(a, 0, n - 1) + 1);
        } else {
            assert(count_neg_range(a, n - 1, n) == 0);
            assert(verifyNeg(a, n) == verifyNeg(a, n - 1));
            assert(count_neg_range(a, 0, n) == count_neg_range(a, 0, n - 1));
        }
    }
}

// Additional lemma to help with the loop step
proof fn lemma_count_step(a: Vec<int>, i: nat)
    requires i < a.len()
    ensures count_neg_range(a, 0, i + 1) == count_neg_range(a, 0, i) + (if a[i] < 0 { 1 } else { 0 })
{
    lemma_count_range_split(a, 0, i, i + 1);
    if a[i] < 0 {
        assert(count_neg_range(a, i, i + 1) == 1);
    } else {
        assert(count_neg_range(a, i, i + 1) == 0);
    }
}

fn CountNeg(a: Vec<int>) -> (cnt: nat)
    ensures
        cnt == verifyNeg(a, a.len())
{
    let mut cnt: nat = 0;
    let mut i: usize = 0;
    
    while i < a.len()
        invariant
            i <= a.len(),
            cnt == count_neg_range(a, 0, i as nat),
    {
        proof {
            lemma_count_step(a, i as nat);
        }
        
        if a[i] < 0 {
            cnt = cnt + 1;
        }
        i = i + 1;
    }
    
    // After the loop, i == a.len() and cnt == count_neg_range(a, 0, a.len())
    // We need to prove that count_neg_range(a, 0, a.len()) == verifyNeg(a, a.len())
    proof {
        lemma_count_equivalence(a, a.len());
        // This establishes verifyNeg(a, a.len()) == count_neg_range(a, 0, a.len())
        // Combined with the loop invariant cnt == count_neg_range(a, 0, a.len()),
        // we get cnt == verifyNeg(a, a.len())
    }
    
    cnt
}

fn main() {
}

}