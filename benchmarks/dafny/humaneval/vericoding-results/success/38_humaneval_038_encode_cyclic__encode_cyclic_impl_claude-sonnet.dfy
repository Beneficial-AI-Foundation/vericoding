// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method encode_cyclic(s: seq<int>) returns (res: seq<int>) 

    ensures |s| == |res|
    ensures forall i :: 0 <= i < |s| - |s| % 3 ==> (i % 3 == 0 ==> res[i] == s[i + 1])
    ensures forall i :: 0 <= i < |s| - |s| % 3 ==> (i % 3 == 1 ==> res[i] == s[i + 1])
    ensures forall i :: 0 <= i < |s| - |s| % 3 ==> (i % 3 == 2 ==> res[i] == s[i - 2])
    ensures forall i :: |s| - |s| % 3 <= i < |s| ==> (res[i] == s[i])
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): fix type error by using seq constructor instead of array */
    res := seq(|s|, i => 0);
    var temp := res;
    var i := 0;
    while i < |s| - |s| % 3
        invariant 0 <= i <= |s| - |s| % 3
        invariant |temp| == |s|
        invariant forall j :: 0 <= j < i && j % 3 == 0 ==> temp[j] == s[j + 1]
        invariant forall j :: 0 <= j < i && j % 3 == 1 ==> temp[j] == s[j + 1]
        invariant forall j :: 0 <= j < i && j % 3 == 2 ==> temp[j] == s[j - 2]
    {
        if i % 3 == 0 {
            temp := temp[i := s[i + 1]];
        } else if i % 3 == 1 {
            temp := temp[i := s[i + 1]];
        } else {
            temp := temp[i := s[i - 2]];
        }
        i := i + 1;
    }
    while i < |s|
        invariant |s| - |s| % 3 <= i <= |s|
        invariant |temp| == |s|
        invariant forall j :: 0 <= j < |s| - |s| % 3 && j % 3 == 0 ==> temp[j] == s[j + 1]
        invariant forall j :: 0 <= j < |s| - |s| % 3 && j % 3 == 1 ==> temp[j] == s[j + 1]
        invariant forall j :: 0 <= j < |s| - |s| % 3 && j % 3 == 2 ==> temp[j] == s[j - 2]
        invariant forall j :: |s| - |s| % 3 <= j < i ==> temp[j] == s[j]
    {
        temp := temp[i := s[i]];
        i := i + 1;
    }
    res := temp;
}
// </vc-code>
