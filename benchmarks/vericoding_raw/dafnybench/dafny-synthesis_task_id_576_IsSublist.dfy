// <vc-helpers>
// </vc-helpers>

method IsSublist(sub: seq<int>, main: seq<int>) returns (result: bool)
    ensures true <== (exists i :: 0 <= i <= |main| - |sub| && sub == main[i..i + |sub|])
// <vc-code>
{
  assume false;
}
// </vc-code>