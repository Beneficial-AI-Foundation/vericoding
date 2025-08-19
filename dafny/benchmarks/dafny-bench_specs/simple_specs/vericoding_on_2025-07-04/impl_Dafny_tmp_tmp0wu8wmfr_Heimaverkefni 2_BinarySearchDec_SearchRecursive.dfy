// IMPL
// Author of question: Snorri Agnarsson
// Permalink of question: https://rise4fun.com/Dafny/CGB1z

// Authors of solution:  Alexander Guðmundsson
// Permalink of solution: https://rise4fun.com/Dafny/VnB5

// Use the command
//  dafny H2-skeleton.dfy
// or
//  compile H2-skeleton.dfy
// to compile the file.
// Or use the web page rise4fun.com/dafny.

// When you have solved the problem put
// the solution on the Dafny web page,
// generate a permalink and put it in
// this file.

method SearchRecursive( a: seq<real>, i: int, j: int, x: real ) returns ( k: int )
  requires 0 <= i <= j <= |a|
  requires forall p, q :: i <= p < q < j ==> a[p] >= a[q]
  ensures i <= k <= j
  ensures forall r | i <= r < k :: a[r] >= x
  ensures forall r | k <= r < j :: a[r] < x
{
  if i == j {
    /* code modified by LLM (iteration 1): Added assertion to help verify postconditions for base case */
    k := i;
    // When i == j, the ranges i <= r < k and k <= r < j are both empty
    // so the postconditions are vacuously true
    assert forall r | i <= r < k :: a[r] >= x;
    assert forall r | k <= r < j :: a[r] < x;
  } else if a[i] < x {
    /* code modified by LLM (iteration 1): Added assertion to help verify postconditions when a[i] < x */
    k := i;
    // When k == i, the range i <= r < k is empty, so first postcondition is vacuously true
    assert forall r | i <= r < k :: a[r] >= x;
    // For the second postcondition, we need to show that all elements from i to j-1 are < x
    // We know a[i] < x, and by the non-increasing property, all subsequent elements are <= a[i] < x
    assert forall r | k <= r < j :: a[r] < x by {
      forall r | k <= r < j 
        ensures a[r] < x
      {
        if r > i {
          // Use the non-increasing property: a[i] >= a[r]
          assert a[i] >= a[r];
          assert a[r] <= a[i] < x;
        } else {
          // r == i == k, so a[r] == a[i] < x
          assert a[r] < x;
        }
      }
    }
  } else {
    /* code modified by LLM (iteration 1): Enhanced recursive case with better verification support */
    // We know a[i] >= x from the else condition
    assert a[i] >= x;
    
    k := SearchRecursive(a, i + 1, j, x);
    
    // From the recursive call, we know:
    assert i + 1 <= k <= j;
    assert forall r | i + 1 <= r < k :: a[r] >= x;
    assert forall r | k <= r < j :: a[r] < x;
    
    // Now establish the postconditions for the current call
    // First postcondition: i <= k <= j (follows from i + 1 <= k and i < i + 1)
    assert i <= k <= j;
    
    // Second postcondition: forall r | i <= r < k :: a[r] >= x
    assert forall r | i <= r < k :: a[r] >= x by {
      forall r | i <= r < k 
        ensures a[r] >= x
      {
        if r == i {
          assert a[r] >= x; // We established a[i] >= x above
        } else {
          assert i + 1 <= r < k;
          assert a[r] >= x; // From recursive call postcondition
        }
      }
    }
    
    // Third postcondition: forall r | k <= r < j :: a[r] < x
    // This follows directly from the recursive call
    assert forall r | k <= r < j :: a[r] < x;
  }
}