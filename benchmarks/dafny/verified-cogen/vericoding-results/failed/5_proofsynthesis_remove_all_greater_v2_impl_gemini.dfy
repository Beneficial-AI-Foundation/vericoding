// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method RemoveAllGreater(v: array<int>, e: int) returns (result: array<int>)
    requires 
        forall k1, k2 :: 0 <= k1 < k2 < v.Length ==> v[k1] != v[k2]
    ensures
        forall k :: 0 <= k < result.Length ==> result[k] <= e && (exists j :: 0 <= j < v.Length && v[j] == result[k])
    ensures
        forall k :: 0 <= k < v.Length && v[k] <= e ==> (exists j :: 0 <= j < result.Length && result[j] == v[k])
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed syntax in sequence comprehension from 'where' to ',' */
    var s: seq<int> := [];
    var i := 0;
    while i < v.Length
        invariant 0 <= i <= v.Length
        invariant multiset(s) == multiset([x | x <- v[..i], x <= e])
        invariant forall y :: y in s ==> exists j :: 0 <= j < i && v[j] == y
        invariant forall k1, k2 :: 0 <= k1 < k2 < |s| ==> s[k1] != s[k2]
    {
        if v[i] <= e {
            s := s + [v[i]];
        }
        i := i + 1;
    }
    result := new int[|s|];
    var j := 0;
    while j < |s|
        invariant 0 <= j <= |s|
        invariant result[..j] == s[..j]
        invariant forall k :: 0 <= k < j ==> result[k] <= e
        invariant forall k :: 0 <= k < j ==> exists l :: 0 <= l < v.Length && v[l] == result[k]
    {
        result[j] := s[j];
        j := j + 1;
    }
}
// </vc-code>
