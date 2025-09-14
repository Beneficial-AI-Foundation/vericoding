// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method SplitStringIntoChars(s: string) returns (v: seq<char>)
    ensures |v| == |s|
    ensures forall i :: 0 <= i < |s| ==> v[i] == s[i]
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): simplified to direct assignment since string is an alias for seq<char> */
  v := s;
}
// </vc-code>
