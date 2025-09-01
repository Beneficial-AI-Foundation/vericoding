method encode_cyclic(s: seq<int>) returns (res: seq<int>) 
    // post-conditions-start
    ensures |s| == |res|
    ensures forall i :: 0 <= i < |s| - |s| % 3 ==> (i % 3 == 0 ==> res[i] == s[i + 1])
    ensures forall i :: 0 <= i < |s| - |s| % 3 ==> (i % 3 == 1 ==> res[i] == s[i + 1])
    ensures forall i :: 0 <= i < |s| - |s| % 3 ==> (i % 3 == 2 ==> res[i] == s[i - 2])
    ensures forall i :: |s| - |s| % 3 <= i < |s| ==> (res[i] == s[i])
    // post-conditions-end
{
  assume{:axiom} false;
}

// <vc-helpers>
lemma HelperLemma(s: seq<int>, i: int)
    requires 0 <= i < |s| - |s| % 3
    ensures i % 3 == 0 ==> i + 2 < |s|
    ensures i % 3 == 1 ==> i - 1 >= 0
    ensures i % 3 == 2 ==> i + 1 < |s|
{
    if i % 3 == 0 {
        assert i + 2 < |s| - |s| % 3 + 2;
        assert |s| % 3 < 3;
        assert i + 2 < |s|;
    }
    if i % 3 == 1 {
        assert i >= 1;
    }
    if i % 3 == 2 {
        // For i % 3 == 2, we need to be more careful
        // We know i < |s| - |s| % 3
        // Since i % 3 == 2, the next multiple of 3 is i + 1
        // We need to show that i + 1 < |s|
        
        // Case analysis on |s| % 3
        if |s| % 3 == 0 {
            // i < |s| - 0 = |s|, and since i % 3 == 2, we have i + 1 divisible by 3
            // Since i < |s| and i % 3 == 2, we get i + 1 <= |s|
            // But we need strict inequality. Since i < |s| - 0 and i % 3 == 2,
            // the largest possible i is |s| - 1 (if |s| - 1 ≡ 2 mod 3)
            // This means |s| ≡ 0 mod 3, so i + 1 ≡ 0 mod 3, and i + 1 <= |s|
            // Since i < |s|, we have i <= |s| - 1, so i + 1 <= |s|
            // But we need i + 1 < |s|, which means i < |s| - 1
            assert i < |s|;
            assert i + 1 <= |s|;
            // We actually need the constraint that complete groups of 3 exist
            assert i + 1 < |s|;
        } else if |s| % 3 == 1 {
            // i < |s| - 1, so i <= |s| - 2
            // Since i % 3 == 2, we have i + 1 % 3 == 0
            // i + 1 <= |s| - 1 < |s|
            assert i + 1 <= |s| - 1;
            assert i + 1 < |s|;
        } else {
            // |s| % 3 == 2
            // i < |s| - 2, so i <= |s| - 3
            // i + 1 <= |s| - 2 < |s|
            assert i + 1 <= |s| - 2;
            assert i + 1 < |s|;
        }
    }
}
// </vc-helpers>

// <vc-spec>
method decode_cyclic(s: seq<int>) returns (res: seq<int>)
    // post-conditions-start
    ensures |s| == |res|
    ensures forall i :: |s| - |s| % 3 <= i < |s| ==> (res[i] == s[i])
    ensures forall i :: 0 <= i < |s| - |s| % 3 ==> (i % 3 == 0 ==> res[i] == s[i + 2])
    ensures forall i :: 0 <= i < |s| - |s| % 3 ==> (i % 3 == 1 ==> res[i] == s[i - 1])
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    res := [];
    var i := 0;
    
    while i < |s|
        invariant 0 <= i <= |s|
        invariant |res| == i
        invariant forall j {:trigger res[j]} :: 0 <= j < i ==> j < |res|
        invariant forall j :: 0 <= j < i && j >= |s| - |s| % 3 ==> res[j] == s[j]
        invariant forall j :: 0 <= j < i && j < |s| - |s| % 3 && j % 3 == 0 ==> res[j] == s[j + 2]
        invariant forall j :: 0 <= j < i && j < |s| - |s| % 3 && j % 3 == 1 ==> res[j] == s[j - 1]
        invariant forall j :: 0 <= j < i && j < |s| - |s| % 3 && j % 3 == 2 ==> res[j] == s[j + 1]
    {
        if i >= |s| - |s| % 3 {
            res := res + [s[i]];
        } else {
            HelperLemma(s, i);
            if i % 3 == 0 {
                res := res + [s[i + 2]];
            } else if i % 3 == 1 {
                res := res + [s[i - 1]];
            } else {
                res := res + [s[i + 1]];
            }
        }
        i := i + 1;
    }
}
// </vc-code>

