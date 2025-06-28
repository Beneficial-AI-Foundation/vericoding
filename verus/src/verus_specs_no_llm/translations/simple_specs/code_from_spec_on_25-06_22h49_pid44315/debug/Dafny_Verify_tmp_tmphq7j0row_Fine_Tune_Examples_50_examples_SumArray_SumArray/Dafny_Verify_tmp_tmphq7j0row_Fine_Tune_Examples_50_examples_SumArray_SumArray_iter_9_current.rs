use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn Sum(arr: Vec<int>, n: nat) -> int
    decreases n
{
    if n == 0 {
        0
    } else if n <= arr.len() {
        arr[(n - 1) as int] + Sum(arr, (n - 1) as nat)
    } else {
        0  // Handle out-of-bounds case
    }
}

proof fn lemma_sum_extend(arr: Vec<int>, n: nat)
    requires n < arr.len()
    ensures Sum(arr, n + 1) == arr[n as int] + Sum(arr, n)
{
    // The proof follows from the definition of Sum
    // Since n < arr.len(), we have n + 1 <= arr.len()
    // So Sum(arr, n + 1) expands to arr[n] + Sum(arr, n)
    assert(n + 1 > 0);
    assert(n + 1 <= arr.len());
    assert(((n + 1) - 1) as int == n as int);
    assert(((n + 1) - 1) as nat == n);
}

fn SumArray(arr: Vec<int>) -> (sum: int)
    requires
        arr.len() > 0
    ensures
        sum == Sum(arr, arr.len())
{
    let mut sum = 0;
    let mut i: usize = 0;
    
    while i < arr.len()
        invariant
            0 <= i <= arr.len(),
            sum == Sum(arr, i as nat)
    {
        // Store the current values for the proof
        let old_i = i;
        let old_sum = sum;
        
        proof {
            // Before adding arr[i], we have sum == Sum(arr, i)
            // We need to show that after the update, sum == Sum(arr, i + 1)
            assert(i < arr.len());
            lemma_sum_extend(arr, i as nat);
            // Now we know Sum(arr, (i as nat) + 1) == arr[i as int] + Sum(arr, i as nat)
            assert(Sum(arr, (i as nat) + 1) == arr[i as int] + Sum(arr, i as nat));
        }
        
        sum = sum + arr[i as int];
        i = i + 1;
        
        proof {
            // After the updates:
            // sum is now old_sum + arr[old_i]
            // i is now old_i + 1
            // We need to show sum == Sum(arr, i as nat)
            assert(sum == old_sum + arr[old_i as int]);
            assert(i == old_i + 1);
            assert(old_sum == Sum(arr, old_i as nat)); // from loop invariant
            assert(Sum(arr, (old_i as nat) + 1) == arr[old_i as int] + Sum(arr, old_i as nat)); // from lemma
            assert((old_i as nat) + 1 == i as nat);
            assert(sum == arr[old_i as int] + Sum(arr, old_i as nat));
            assert(sum == Sum(arr, i as nat));
        }
    }
    
    sum
}

}