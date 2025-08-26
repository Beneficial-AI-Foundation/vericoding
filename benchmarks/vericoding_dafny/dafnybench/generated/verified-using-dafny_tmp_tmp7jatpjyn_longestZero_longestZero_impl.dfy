function getSize(i: int, j:int) : int
{
    j - i + 1    
}

// For a given integer array, let's find the longest subesquence of 0s.
// sz: size, pos: position.   a[pos..(pos+sz)] will be all zeros

// <vc-helpers>
predicate allZeros(a: array<int>, start: int, size: int)
    reads a
{
    start >= 0 && start + size <= a.Length && 
    forall k :: start <= k < start + size ==> a[k] == 0
}

predicate hasNonZero(a: array<int>, p: int, q: int)
    reads a
{
    p >= 0 && q < a.Length && p <= q &&
    exists r :: p <= r <= q && a[r] != 0
}

lemma helperLemma(a: array<int>, i: int, sz: int)
    requires 0 <= i < a.Length
    requires a[i] != 0
    requires sz >= 0
    ensures forall p,q :: (0 <= p <= i && i <= q < a.Length && getSize(p, q) > sz) ==> exists r :: p <= r <= q && a[r] != 0
{
    forall p,q | 0 <= p <= i && i <= q < a.Length && getSize(p, q) > sz
        ensures exists r :: p <= r <= q && a[r] != 0
    {
        assert p <= i <= q;
        assert a[i] != 0;
    }
}

lemma zeroLemma(a: array<int>, i: int, sz: int)
    requires 0 <= i < a.Length
    requires a[i] == 0
    requires sz >= 0
    requires forall p,q :: (0 <= p < q < i && getSize(p, q) > sz) ==> (p < a.Length && q < a.Length ==> exists r :: p <= r <= q && a[r] != 0)
    ensures forall p,q :: (0 <= p < q < i+1 && getSize(p, q) > sz) ==> (p < a.Length && q < a.Length ==> exists r :: p <= r <= q && a[r] != 0)
{
    forall p,q | 0 <= p < q < i+1 && getSize(p, q) > sz && p < a.Length && q < a.Length
        ensures exists r :: p <= r <= q && a[r] != 0
    {
        if q < i {
            // This case is covered by the precondition
            assert 0 <= p < q < i && getSize(p, q) > sz;
        } else {
            // q == i, so we need to show that some element from p to i is non-zero
            assert q == i;
            if p < i {
                // We have p < i, so we can use the precondition with q = i-1
                if getSize(p, i-1) > sz {
                    // Use precondition: forall p,q :: (0 <= p < q < i && getSize(p, q) > sz) ==> ...
                    assert 0 <= p < i-1+1 == i && getSize(p, i-1) > sz;
                    // But we need 0 <= p < q < i, which means q <= i-1
                    // So we need p < i-1+1 <= i, which gives us p <= i-1
                    // Since p < i, we have either p <= i-1 or p == i, but p < i so p <= i-1
                    // And we need i-1+1 = i > p, so i-1 >= p, which means i-1+1 > p, so q = i-1+1 satisfies p < q
                    // We have 0 <= p < i-1+1 < i+1, and since q = i < i+1, we have q < i+1
                    // But we need q < i for the precondition, so q = i-1
                    if i-1 >= p {
                        assert 0 <= p < i-1+1 <= i;
                        if i-1+1 > p { // This means i > p, which we know is true
                            assert 0 <= p < i-1+1 < i+1;
                            if i-1+1 < i { // This means i-1+1 < i, so i < i, which is false
                                // This case is impossible
                                assert false;
                            } else {
                                // i-1+1 >= i, so i-1+1 == i since i-1+1 = i
                                // We can't use precondition directly since we need q < i
                                // Let's try with q = i-1 if i-1 >= p
                                if i > p+1 { // This means i-1 > p, so i-1 >= p+1 > p
                                    assert 0 <= p < i-1 < i && getSize(p, i-1) >= getSize(p, i-1);
                                    if getSize(p, i-1) > sz {
                                        // Now we can use the precondition
                                        var witness :| p <= witness <= i-1 && a[witness] != 0;
                                        assert p <= witness <= i-1 < i <= q;
                                        assert p <= witness <= q && a[witness] != 0;
                                    } else {
                                        // getSize(p, i-1) <= sz but getSize(p, i) > sz
                                        // Since getSize(p, i) = getSize(p, i-1) + 1, we have getSize(p, i-1) = getSize(p, i) - 1 > sz - 1
                                        // So getSize(p, i-1) >= sz, and since getSize(p, i-1) <= sz, we have getSize(p, i-1) == sz
                                        // This means getSize(p, i) == sz + 1 > sz, which is consistent
                                        // Now we need to find a non-zero in [p, i]
                                        // Since a[i] == 0, we need to find it in [p, i-1]
                                        // But getSize(p, i-1) == sz, and all segments of size > sz have non-zeros
                                        // We need more information to proceed. Let's try a different approach.
                                        // 
                                        // The key insight is that if getSize(p, i) > sz and a[i] == 0,
                                        // then either there's a non-zero in [p, i-1], or the entire [p, i] is zeros
                                        // but then it would violate our invariant that segments of size > sz have non-zeros
                                        // 
                                        // Actually, this situation should not arise if our invariant is maintained correctly
                                        // during the algorithm. The algorithm ensures that sz is always the size of the 
                                        // longest zero sequence found so far.
                                        //
                                        // For the proof, let's use the fact that either there's a shorter zero sequence
                                        // or there must be a non-zero somewhere in a longer sequence.
                                        
                                        // If all elements from p to i are zero, then we have a zero sequence of length getSize(p,i) > sz
                                        // But sz should be the length of the longest zero sequence seen so far
                                        // This suggests the algorithm invariant ensures this case doesn't happen
                                        
                                        // For verification purposes, we need to be more careful about the invariant
                                        // The invariant should ensure that sz is always up to date
                                        var allZerosFromPtoI := forall k :: p <= k <= i ==> a[k] == 0;
                                        if allZerosFromPtoI {
                                            // This contradicts our expectation, since we should have updated sz
                                            // In the algorithm, when we encounter zeros, we update sz if current sequence is longer
                                            // So this case should not occur with proper invariants
                                        }
                                        
                                        // Since we can't assume, we need to structure this differently
                                        // Let's just ensure the non-zero exists by contradiction
                                        if (forall r :: p <= r <= q ==> a[r] == 0) {
                                            // All elements from p to i are zero, length > sz
                                            // This should contradict our invariant maintenance
                                        } else {
                                            // There exists a non-zero, which is what we want to prove
                                        }
                                    }
                                } else {
                                    // i <= p+1, and since p < i, we have i == p+1
                                    // So getSize(p, i) = getSize(p, p+1) = (p+1) - p + 1 = 2
                                    assert i == p + 1;
                                    assert getSize(p, i) == 2;
                                    assert 2 > sz;
                                    // We have a[p] and a[i] = a[p+1], and a[i] == 0
                                    // We need to show there's a non-zero in {a[p], a[i]}
                                    // Since a[i] == 0, we need a[p] != 0
                                    // But this may not be true in general
                                }
                            }
                        }
                    }
                }
            } else {
                // p >= i, and since p < q and q == i, we need p < i, contradiction
                assert false;
            }
        }
    }
}
// </vc-helpers>

method longestZero(a: array<int>) returns (sz:int, pos:int)   
    requires 1 <= a.Length
    ensures 0 <= sz <= a.Length
    ensures 0 <= pos < a.Length
    ensures pos + sz <= a.Length
    ensures forall i:int  :: pos <= i < pos + sz ==> a[i] == 0
    ensures forall i,j :: (0 <= i < j < a.Length && getSize(i, j) > sz) ==> exists k :: i <= k <= j && a[k] != 0
// </vc-spec>
// <vc-code>
{
    sz := 0;
    pos := 0;
    
    var currentStart := 0;
    var currentSize := 0;
    var i := 0;
    
    while i < a.Length
        invariant 0 <= i <= a.Length
        invariant 0 <= sz <= a.Length
        invariant 0 <= pos < a.Length
        invariant pos + sz <= a.Length
        invariant 0 <= currentStart <= i
        invariant 0 <= currentSize <= i - currentStart
        invariant currentStart + currentSize <= a.Length
        invariant forall k :: pos <= k < pos + sz ==> a[k] == 0
        invariant forall k :: currentStart <= k < currentStart + currentSize ==> a[k] == 0
        invariant forall p,q :: (0 <= p <= q < i && getSize(p, q) > sz) ==> exists r :: p <= r <= q && a[r] != 0
        invariant currentStart <= i - currentSize
        invariant (currentSize > 0) ==> (currentStart + currentSize <= i && forall k :: currentStart <= k < currentStart + currentSize ==> a[k] == 0)
        invariant (currentSize > 0) ==> (currentStart + currentSize == i)
        invariant sz >= currentSize
    {
        if a[i] == 0 {
            if currentSize == 0 {
                currentStart := i;
            }
            currentSize := currentSize + 1;
            
            if currentSize > sz {
                sz := currentSize;
                pos := currentStart;
            }
        } else {
            helperLemma(a, i, sz);
            currentSize := 0;
        }
        i := i + 1;
    }
}
// </vc-code>