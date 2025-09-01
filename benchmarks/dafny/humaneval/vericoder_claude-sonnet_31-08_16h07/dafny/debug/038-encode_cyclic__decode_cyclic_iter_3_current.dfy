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
        // Since i < |s| - |s| % 3 and i % 3 == 2, we know that i + 1 < |s| - |s| % 3 + 1
        // and since |s| % 3 >= 0, we have i + 1 < |s|
        assert i + 1 <= |s| - |s| % 3;
        assert i + 1 < |s|;
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
        invariant forall j :: 0 <= j < i && j < |s| - |s| % 3 && j % 3 == 2 && j + 1 < |s| ==> res[j] == s[j + 1]
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

