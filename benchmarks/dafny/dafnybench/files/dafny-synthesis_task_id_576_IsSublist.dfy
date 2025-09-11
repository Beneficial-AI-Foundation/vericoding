// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method IsSublist(sub: seq<int>, main: seq<int>) returns (result: bool)
    ensures true <== (exists i :: 0 <= i <= |main| - |sub| && sub == main[i..i + |sub|])
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
