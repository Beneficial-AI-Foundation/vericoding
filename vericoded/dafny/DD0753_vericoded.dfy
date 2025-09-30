

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method SplitAndAppend(l: seq<int>, n: int) returns (r: seq<int>)
    requires n >= 0 && n < |l|
    ensures |r| == |l|
    ensures forall i :: 0 <= i < |l| ==> r[i] == l[(i + n) % |l|]
// </vc-spec>
// <vc-code>
{
    r := l[n..] + l[..n];
    
    // Prove the postcondition
    assert |r| == |l[n..]| + |l[..n]| == (|l| - n) + n == |l|;
    
    forall i | 0 <= i < |l|
    ensures r[i] == l[(i + n) % |l|]
    {
        if i < |l| - n {
            assert r[i] == l[n..][i] == l[n + i];
            assert (i + n) % |l| == i + n;
            assert r[i] == l[(i + n) % |l|];
        } else {
            assert i >= |l| - n;
            assert r[i] == l[..n][i - (|l| - n)];
            assert r[i] == l[i - (|l| - n)];
            assert (i + n) % |l| == (i + n) - |l| == i - (|l| - n);
            assert r[i] == l[(i + n) % |l|];
        }
    }
}
// </vc-code>

