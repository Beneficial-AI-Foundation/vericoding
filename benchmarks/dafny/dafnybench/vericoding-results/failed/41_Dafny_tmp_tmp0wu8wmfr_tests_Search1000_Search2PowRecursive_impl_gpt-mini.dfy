// Author: Snorri Agnarsson, snorri@hi.is

// Search1000 is a Dafny version of a function shown
// by Jon Bentley in his old Programming Pearls
// column in CACM.  Surprisingly Dafny needs no help
// to verify the function.

// Is2Pow(n) is true iff n==2^k for some k>=0.
predicate Is2Pow( n: int )
    decreases n;
{
    if n < 1 then
        false
    else if n == 1 then
        true
    else
        n%2 == 0 && Is2Pow(n/2)
}

// This method is a binary search that only works for array
// segments of size n == 2^k-1 for some k>=0.

// This method is a binary search that only works for array
// segments of size n == 2^k-1 for some k>=0.

// <vc-helpers>
lemma SubrangeSorted(a: array<int>, i: int, n: int, s: int, m: int)
    requires 0 <= i <= i+n <= a.Length
    requires forall p,q | i <= p < q < i+n :: a[p] <= a[q]
    requires i <= s <= s+m <= i+n
    ensures forall p,q | s <= p < q < s+m :: a[p] <= a[q]
{
    forall p,q | s <= p < q < s+m
    {
        assert i <= p;
        assert q < i+n;
        assert a[p] <= a[q];
    }
}

lemma PowerOfTwo_half(n: int)
    requires Is2Pow(n+1)
    requires n > 0
    ensures Is2Pow(n/2 + 1)
    ensures n % 2 == 1
    ensures n - n/2 - 1 == n/2
    ensures 2*(n/2) + 1 == n
    decreases n
{
    var m := n + 1;
    assert Is2Pow(m);
    if m == 1 {
        assert false;
    } else {
        // From Is2Pow(m) and m > 1 we have m % 2 == 0 and Is2Pow(m/2)
        assert m % 2 == 0;
        assert Is2Pow(m/2);
        var t := m/2;
        assert m == 2*t;
        assert n == 2*t - 1;
        // From n = 2*t - 1 we get n/2 == t-1
        assert 2*(t-1) <= n;
        assert n < 2*t;
        assert n/2 == t-1;
        assert n/2 + 1 == t;
        // n is odd
        assert n % 2 == 1;
        // n - n/2 - 1 == n/2
        assert n - n/2 - 1 == t-1;
        assert t-1 == n/2;
        assert n - n/2 - 1 == n/2;
        // And Is2Pow(t) holds, so Is2Pow(n/2 + 1) holds
        assert Is2Pow(n/2 + 1);
        // Provide the equivalent form 2*(n/2) + 1 == n
        assert 2*(n/2) + 1 == n;
    }
}
// </vc-helpers>

// <vc-spec>
method Search2PowRecursive( a: array<int>, i: int, n: int, x: int ) returns ( k: int )
    decreases n;
    requires 0 <= i <= i+n <= a.Length;
    requires forall p,q | i <= p < q < i+n :: a[p] <= a[q];
    requires Is2Pow(n+1);
    ensures i <= k <= i+n;
    ensures forall r | i <= r < k :: a[r] < x;
    ensures forall r | k <= r < i+n :: a[r] >= x;
// </vc-spec>
// <vc-code>
{
  if n == 0 {
    k := i;
    return;
  }
  var j := i + n/2;
  if a[j] < x {
    // Ensure the power-of-two facts for arithmetic reasoning
    assert n > 0;
    PowerOfTwo_half(n);
    var n2 := n/2;
    // Relate j and n2
    assert n2 == n/2;
    assert j == i + n2;
    // From lemma we have n - n2 - 1 == n2 and hence 2*n2 + 1 == n
    assert n - n2 - 1 == n2;
    assert 2*n2 + 1 == n;
    // Bounds for right subrange [j+1, j+1+n2)
    assert j + 1 + n2 == i + n;
    assert 0 <= i;
    assert 0 <= j+1 <= j+1 + n2 <= a.Length;
    // Sortedness on right subrange
    SubrangeSorted(a, i, n, j+1, n2);
    // Decrease argument for recursion
    assert n2 < n;
    k := Search2PowRecursive(a, j+1, n2, x);
    return;
  } else {
    assert n > 0;
    PowerOfTwo_half(n);
    var n2 := n/2;
    // Bounds for left subrange [i, i+n2)
    assert 0 <= i <= i + n2 <= a.Length;
    // Sortedness on left subrange
    SubrangeSorted(a, i, n, i, n2);
    // Decrease argument for recursion
    assert n2 < n;
    k := Search2PowRecursive(a, i, n2, x);
    return;
  }
}
// </vc-code>

