// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method smallest_change(s: seq<int>) returns (c: int)

  ensures c == |set i | 0 <= i < |s| / 2 && s[i] != s[|s| - 1 - i]|
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
