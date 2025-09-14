

// <vc-helpers>
function ContainsSeq(s: seq<int>, x: int) : bool
{
  exists i :: 0 <= i < |s| && s[i] == x
}
// </vc-helpers>

// <vc-spec>
method RemoveDuplicates(a: array<int>) returns (result: seq<int>)
    requires a != null
    ensures forall x :: x in result <==> exists i :: 0 <= i < a.Length && a[i] == x
    ensures forall i, j :: 0 <= i < j < |result| ==> result[i] != result[j]
// </vc-spec>
// <vc-code>
{
    var s: seq<int> := [];
    var i := 0;
    while i < a.Length
      invariant 0 <= i <= a.Length
      invariant forall x :: x in s <==> (exists k :: 0 <= k < i && a[k] == x)
      invariant forall i_s, j_s :: 0 <= i_s < j_s < |s| ==> s[i_s] != s[j_s]
    {
        if !(ContainsSeq(s, a[i])) {
            s := s + [a[i]];
        }
        i := i + 1;
    }
    return s;
}
// </vc-code>

