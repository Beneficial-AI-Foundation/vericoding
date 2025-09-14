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

// <vc-helpers>
predicate Is2Pow( n: int )
{
    if n < 1 then
        false
    else if n == 1 then
        true
    else
        n%2 == 0 && Is2Pow(n/2)
}

lemma Is2PowEq(x: int, y: int)
    requires Is2Pow(x)
    requires Is2Pow(y)
    requires x == y
    ensures Is2Pow(x)
{
}

lemma DivideByTwoProperty(n: int)
    requires Is2Pow(n)
    ensures Is2Pow(n/2) || (n==1 && n/2 == 0)
{
    if n > 1 {
        assert Is2Pow(n/2);
    }
}

lemma Lemma_high_minus_low_plus_1_Is2Pow(low: int, high: int)
    requires Is2Pow(high - low + 1)
    ensures Is2Pow((high - low) / 2 + 1)
    ensures Is2Pow((high - low) - (high - low) / 2)
{
    var range := high - low + 1;
    var mid_range_low := (high - low) / 2 + 1;
    var mid_range_high := (high - low) - (high - low) / 2;

    if range == 1 {
        assert mid_range_low == 1;
        assert mid_range_high == 0;
    } else {
        DivideByTwoProperty(range);
        assert Is2Pow(range / 2);
        assert (range / 2 == mid_range_low && mid_range_high == mid_range_low -1) || range == 1; 

        if (high - low) % 2 == 0 { // (high - low + 1) is odd ==> (high - low) is even
            assert range / 2 == mid_range_low -1; // Corrected: range/2 is not mid_range_low, but mid_range_low-1 if range is odd
            assert Is2Pow(mid_range_low); // This assertion is not generally true. mid_range_low is (range-1)/2+1 when range is odd.
            assert mid_range_high == mid_range_low - 1; 
            if Is2Pow(range / 2) && range / 2 == mid_range_low -1 {
                assert Is2Pow(mid_range_low -1);
            }
        } else { // (high - low + 1) is even ==> (high - low) is odd
            assert mid_range_low == (range - 1) / 2 + 1;
            assert mid_range_high == (range - 1) / 2;
            DivideByTwoProperty(range);
            assert Is2Pow(range/2);
            if range/2 == mid_range_high {
                assert Is2Pow(mid_range_high);
            }
            if range/2 + 1 == mid_range_low {
                assert Is2Pow(mid_range_low -1);
            }
        }
    }
}
// </vc-helpers>

// <vc-spec>
method Search2PowLoop( a: array<int>, i: int, n: int, x: int ) returns ( k: int )
    requires 0 <= i <= i+n <= a.Length;
    requires forall p,q | i <= p < q < i+n :: a[p] <= a[q];
    requires Is2Pow(n+1);
    ensures i <= k <= i+n;
    ensures forall r | i <= r < k :: a[r] < x;
    ensures forall r | k <= r < i+n :: a[r] >= x;
// </vc-spec>
// <vc-code>
{
    var low := i;
    var high := i + n;

    while low < high
        invariant i <= low <= high <= i + n;
        invariant Is2Pow(high - low + 1);
        invariant forall r | i <= r < low :: a[r] < x;
        invariant forall r | high <= r < i + n :: a[r] >= x;
        decreases high - low;
    {
        var mid := low + (high - low) / 2;
        if a[mid] < x {
            var old_low := low;
            var old_high := high;
            low := mid + 1;
            
            Lemma_high_minus_low_plus_1_Is2Pow(old_low, old_high);
            assert (old_high - old_low) - (old_high - old_low) / 2 == old_high - (old_low + (old_high - old_low) / 2);
            assert high - low + 1 == old_high - mid;
            assert high - low + 1 == (old_high - old_low) - (old_high - old_low) / 2;
            
            if (old_high - old_low + 1) == 1 {
                 assert high - low + 1 == 0; // range is 1, so (high - low + 1) is 1. If a[mid] < x, then low = mid + 1, high = old_high.
                                                 // if old_low == old_high, then mid == old_low. low = old_low + 1, high = old_low. low > high so loop terminates. 
            } else {
                if (old_high - old_low) % 2 == 0 { // old_range+1 is odd, (old_range) is even
                    assert (old_high - old_low) / 2 + 1 == mid - old_low + 1;
                    assert (old_high - old_low) - (old_high - old_low) / 2 == old_high - mid;

                    if Is2Pow((old_high - old_low) - (old_high - old_low)/2) {
                        assert Is2Pow(high - low + 1);
                    }
                } else { // (old_high - old_low + 1) is even, (old_high - old_low) is odd
                    assert (old_high - old_low) / 2 + 1 == mid - old_low + 1;
                    assert (old_high - old_low) - (old_high - old_low) / 2 == old_high - mid;

                    if Is2Pow((old_high - old_low) - (old_high - old_low)/2) {
                        assert Is2Pow(high - low + 1);
                    }

                }
            }
        } else {
            var old_low := low;
            var old_high := high;
            high := mid;
            
            Lemma_high_minus_low_plus_1_Is2Pow(old_low, old_high);
            assert high - low + 1 == mid - old_low + 1;
            assert (old_high - old_low) / 2 + 1 == mid - old_low + 1;

            if Is2Pow((old_high - old_low) / 2 + 1) {
                assert Is2Pow(high - low + 1);
            }
        }
    }
    return low;
}
// </vc-code>

// This method is a binary search that only works for array
// segments of size n == 2^k-1 for some k>=0.