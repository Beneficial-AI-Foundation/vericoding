// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// VSComp 2010, problem 1, compute the sum and max of the elements of an array and prove
// that 'sum <= N * max'.
// Rustan Leino, 18 August 2010.
//
// The problem statement gave the pseudo-code for the method, but did not ask to prove
// that 'sum' or 'max' return as the sum and max, respectively, of the array.  The
// given assumption that the array's elements are non-negative is not needed to establish
// the requested postcondition.

// <vc-helpers>
lemma sum_le_N_max(a: array<int>, N: int, sum: int, max: int)
  requires 0 <= N && a.Length == N;
  requires N > 0 ==> (forall k :: 0 <= k < N ==> 0 <= a[k]); // Only need non-negative for N>0 case, or sum/max might be negative
  requires sum == (sum k :: 0 <= k < N :: a[k]);
  requires N == 0 ==> sum == 0 && max == 0; // If N is 0, sum and max must be 0
  requires N > 0 ==> (exists k :: 0 <= k < N && max == a[k]); // For N>0, max must be one of the elements
  requires N > 0 ==> (forall k :: 0 <= k < N ==> a[k] <= max); // For N>0, all elements must be <= max
  ensures sum <= N * max;
{
  if N == 0 {
    assert sum == 0;
    assert max == 0;
    assert sum <= N * max; // 0 <= 0 * 0 holds
  } else {
    // For each k, a[k] <= max where 0 <= k < N.
    // Sum is sum_k a[k].
    // Since a[k] <= max, sum_k a[k] <= sum_k max.
    // sum_k max is N * max.
    // So sum <= N * max.
    calc {
      sum;
      (sum k :: 0 <= k < N :: a[k]);
      <= (sum k :: 0 <= k < N :: max);
      N * max;
    }
  }
}
// </vc-helpers>

// <vc-spec>
method M(N: int, a: array<int>) returns (sum: int, max: int)
  requires 0 <= N && a.Length == N && (forall k :: 0 <= k && k < N ==> 0 <= a[k]);
  ensures sum <= N * max;
// </vc-spec>
// <vc-code>
{
    sum := 0;
    max := 0;

    if N > 0 {
        max := a[0];
    }

    var i := 0;
    while i < N
        invariant 0 <= i <= N;
        invariant sum == (sum k :: 0 <= k < i :: a[k]);
        invariant N == 0 ==> sum == 0 && max == 0;
        invariant N > 0 && i == 0 ==> max == a[0]; // If i=0, max is just a[0] (if N>0)
        invariant N > 0 && i > 0 ==> (exists k :: 0 <= k < i && max == a[k]);
        invariant N > 0 ==> (forall k :: 0 <= k < i ==> a[k] <= max);
    {
        if (i == 0 && N > 0) || (N > 0 && a[i] > max) { // Simplified the check such that max is updated correctly
            max := a[i];
        }
        sum := sum + a[i];
        i := i + 1;
    }

    if N > 0 {
      assert sum == (sum k :: 0 <= k < N :: a[k]);
      assert (forall k :: 0 <= k < N ==> a[k] <= max);
      assert (exists k :: 0 <= k < N && max == a[k]); // Derived from initial setting of max and update rule.
      sum_le_N_max(a, N, sum, max);
    } else {
      assert N == 0;
      assert sum == 0;
      assert max == 0;
      sum_le_N_max(a, N, sum, max);
    }
}
// </vc-code>

