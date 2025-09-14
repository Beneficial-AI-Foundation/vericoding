

// <vc-helpers>
function StringToSeq(s: string): seq<char>
  decreases |s|
  ensures |StringToSeq(s)| == |s|
  ensures forall i :: 0 <= i < |s| ==> StringToSeq(s)[i] == s[i]
{
  if |s| == 0 then []
  else [s[0]] + StringToSeq(s[1..])
}
// </vc-helpers>

// <vc-spec>
method SplitStringIntoChars(s: string) returns (v: seq<char>)
    ensures |v| == |s|
    ensures forall i :: 0 <= i < |s| ==> v[i] == s[i]
// </vc-spec>
// <vc-code>
{
  v := StringToSeq(s);
}
// </vc-code>

