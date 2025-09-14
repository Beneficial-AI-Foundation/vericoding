

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method InsertBeforeEach(s: seq<string>, x: string) returns (v: seq<string>)
        ensures |v| == 2 * |s|
        ensures forall i :: 0 <= i < |s| ==> v[2*i] == x && v[2*i + 1] == s[i]
// </vc-spec>
// <vc-code>
{
    var new_v: seq<string> := [];
    var i := 0;
    while i < |s|
        invariant 0 <= i <= |s|
        invariant |new_v| == 2 * i
        invariant forall k :: 0 <= k < i ==> new_v[2*k] == x && new_v[2*k + 1] == s[k]
    {
        new_v := new_v + [x, s[i]];
        i := i + 1;
    }
    return new_v;
}
// </vc-code>

