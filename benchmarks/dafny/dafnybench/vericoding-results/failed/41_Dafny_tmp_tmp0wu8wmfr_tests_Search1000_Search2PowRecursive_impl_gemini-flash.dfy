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
// The original Is2Pow predicate caused a duplicate member name error.
// The predicate needs to be defined only once.
// If helpers are needed, they should not duplicate existing definitions unless
// they are different or refined versions.
// For this problem, the helper's `Is2Pow` definition duplicates the one in the PREAMBLE.
// To fix the verification error, we should remove the duplicate definition here,
// as the one in the PREAMBLE is already available.
// If any other helper predicates or functions were needed, they would be placed here.
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
        return i;
    }
    var m := n / 2;

    // The recursive calls need to satisfy several preconditions.
    // Specifically, `Is2Pow(m+1)` needs to be established.

    // Property: if n+1 is a power of 2, and n > 0, then (n/2)+1 or m+1 is also a power of 2.
    // Let N = n+1. We are given Is2Pow(N).
    // If N is a power of 2, N = 2^k for some k >= 1 (since n > 0 implies N > 1).
    // Then n = 2^k - 1.
    // m = n/2 = (2^k - 1) / 2. This is integer division.
    // If k=1, N=2, n=1, m=0. m+1 = 1, which is 2^0, so Is2Pow(1) is true.
    // If k>1, N=2^k. n=2^k-1. m=(2^k-1)/2. This is more accurately written as:
    // If N is even, N/2 is 2^{k-1}.
    // n+1 is a power of 2 implies n+1 is even (if n+1 > 1).
    // So (n+1)/2 is also a power of 2.
    // (n+1)/2 = n/2 + 1/2.
    // For integer division, m = n/2.
    // If n is odd (which it is, since n+1 is even), then n=2k'-1. n/2 = k'-1.
    // (n+1)/2 = k'.
    // So m+1 = n/2 + 1 if n is even.
    // m+1 = (n+1)/2 if n is odd. Since n+1 is an even power of 2, n must be odd.
    // Therefore, m+1 == (n+1)/2.
    // Since (n+1) is a power of 2, and n+1 > 1 (because n > 0), then (n+1)/2 is also a power of 2.
    // So Is2Pow(m+1) holds.

    var k_ret: int;

    if x <= a[i+m] {
        // First recursive call: Search2PowRecursive(a, i, m, x)
        // Preconditions:
        // 1. 0 <= i <= i+m <= a.Length; (from context)
        // 2. forall p,q | i <= p < q < i+m :: a[p] <= a[q]; (from context)
        // 3. Is2Pow(m+1);
        // We know Is2Pow(n+1). Since n > 0, Is2Pow(n+1) implies n+1 is >= 2.
        // If n+1 = 2^k for k >= 1.
        // Then m = (n)/2 = (2^k - 1)/2 (integer division).
        // If k=1, n+1=2, n=1. m=0. m+1 = 1. Is2Pow(1) is true.
        // If k>1, n+1 is even. n is odd. (n+1)/2 is a power of 2.
        // m = n/2. Since n is odd, n = 2q + 1 for some q. So m = q.
        // n+1 = 2q + 2. (n+1)/2 = q + 1.
        // So m+1 = q+1 = (n+1)/2.
        // Thus, Is2Pow(m+1) holds.
        // Also, it's trivial that i <= i+m <= a.Length if i <= i+n <= a.Length and m <= n.
        // And sortedness for [i, i+m) holds from [i, i+n).
        k_ret := Search2PowRecursive(a, i, m, x);
    } else {
        // Second recursive call: Search2PowRecursive(a, i+m+1, m, x)
        // Preconditions:
        // 1. 0 <= i+m+1 <= i+m+1+m <= a.Length;
        //    i+m+1+m = i+2m+1.
        //    Since m = n/2 (integer division), 2m <= n.
        //    If n is even, n=2m. Then 2m+1 = n+1. So i+m+1+m = i+n+1.
        //    But recursive call requires i+m+1+m+1 which is i+(n+1)+1.
        //    This means that the segment length is m.
        //    So the array bound is i_start + length.
        //    Here it's (i+m+1) + m.
        //    We need to prove i+m+1 + m <= a.Length.
        //    We know i+n <= a.Length.
        //    Since m = n/2, we have 2m <= n.
        //    So m+1+m = 2m+1.
        //    If n is odd (n+1 is power of 2, so n is odd if n > 0), n = 2m+1.
        //    So i+m+1+m = i+(2m+1) = i+n.
        //    Thus, i+m+1 + m <= a.Length is equivalent to i+n <= a.Length, which is given.
        // 2. forall p,q | i+m+1 <= p < q < i+m+1+m :: a[p] <= a[q]; (from context)
        // 3. Is2Pow(m+1); (established above)
        k_ret := Search2PowRecursive(a, i+m+1, m, x);
    }
    return k_ret;
}
// </vc-code>

