function getSize(i: int, j:int) : int
{
    j - i + 1    
}

// For a given integer array, let's find the longest subesquence of 0s.
// sz: size, pos: position.   a[pos..(pos+sz)] will be all zeros

// <vc-helpers>
// Helper lemma to prove properties about subarrays
lemma SubArrayProperty(a: array<int>, i: int, j: int, sz: int, pos: int)
    requires 1 <= a.Length
    requires 0 <= i <= j < a.Length
    requires 0 <= pos < a.Length
    requires 0 <= sz <= a.Length
    requires pos + sz <= a.Length
    requires forall k :: pos <= k < pos + sz ==> a[k] == 0
    requires getSize(i, j) > sz
    ensures exists k :: i <= k <= j && a[k] != 0
{
    if i >= pos && j < pos + sz {
        // If the range [i, j] is completely within [pos, pos+sz), it contradicts getSize(i, j) > sz
        // since all elements in [pos, pos+sz) are 0, but getSize(i,j) > sz implies a larger size.
        assert false;
    } else {
        if i < pos {
            assert i <= pos - 1 <= j;
            if pos > 0 {
                assert pos - 1 >= 0;
                if !(pos - 1 < pos + sz && a[pos - 1] == 0) {
                    assert i <= pos - 1 <= j && a[pos - 1] != 0;
                    return;
                }
            }
        }
        if j >= pos + sz {
            assert i <= pos + sz <= j;
            if pos + sz < a.Length {
                if a[pos + sz] != 0 {
                    assert i <= pos + sz <= j && a[pos + sz] != 0;
                    return;
                }
            }
        }
        // If no contradiction, recurse or find a non-zero outside [pos, pos+sz)
        var k := if i < pos then pos - 1 else pos + sz;
        if i <= k <= j && 0 <= k < a.Length && a[k] != 0 {
            assert i <= k <= j && a[k] != 0;
        } else {
            assert exists k :: i <= k <= j && a[k] != 0;
        }
    }
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
method longestZero(a: array<int>) returns (sz:int, pos:int)   
    requires 1 <= a.Length
    ensures 0 <= sz <= a.Length
    ensures 0 <= pos < a.Length
    ensures pos + sz <= a.Length
    ensures forall i:int  :: pos <= i < pos + sz ==> a[i] == 0
    ensures forall i,j :: (0 <= i < j < a.Length && getSize(i, j) > sz) ==> exists k :: i <= k <= j && a[k] != 0
// </vc-spec>
// </vc-spec>

// <vc-code>
method LongestZero(a: array<int>) returns (sz: int, pos: int)
    requires 1 <= a.Length
    ensures 0 <= sz <= a.Length
    ensures 0 <= pos < a.Length
    ensures pos + sz <= a.Length
    ensures forall i: int :: pos <= i < pos + sz ==> a[i] == 0
    ensures forall i, j :: (0 <= i < j < a.Length && getSize(i, j) > sz) ==> exists k :: i <= k <= j && a[k] != 0
{
    sz := 0;
    pos := 0;
    var maxSz := 0;
    var maxPos := 0;
    var i := 0;

    while i < a.Length
        invariant 0 <= i <= a.Length
        invariant 0 <= maxSz <= i
        invariant 0 <= maxPos < a.Length
        invariant maxPos + maxSz <= a.Length
        invariant forall k: int :: maxPos <= k < maxPos + maxSz ==> a[k] == 0
        invariant forall p, q :: (0 <= p <= q < i && getSize(p, q) > maxSz) ==> exists k :: p <= k <= q && a[k] != 0
    {
        if a[i] == 0 {
            var start := i;
            var currSz := 0;
            while i < a.Length && a[i] == 0
                invariant start <= i <= a.Length
                invariant currSz == i - start
                invariant forall k: int :: start <= k < i ==> a[k] == 0
            {
                i := i + 1;
                currSz := currSz + 1;
            }
            if currSz > maxSz {
                maxSz := currSz;
                maxPos := start;
            }
        } else {
            // For any range ending at i that is larger than maxSz, use the current non-zero element
            var p := 0;
            var q := i;
            if i > 0 && 0 <= p <= q < a.Length && getSize(p, q) > maxSz {
                assert a[i] != 0;
                assert p <= i <= q && a[i] != 0;
            }
            i := i + 1;
        }
    }
    sz := maxSz;
    pos := maxPos;
    // Final check for postcondition using the lemma
    var p, q := 0, a.Length - 1;
    if 0 <= p <= q < a.Length && getSize(p, q) > maxSz {
        SubArrayProperty(a, p, q, maxSz, maxPos);
    }
}
// </vc-code>
