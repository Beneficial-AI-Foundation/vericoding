

// <vc-helpers>
function {:inline} SublistExists(sub: seq<int>, main: seq<int>): bool
{
  exists i {:trigger main[i..i + |sub|]} :: 0 <= i <= |main| - |sub| && sub == main[i..i + |sub|]
}
// </vc-helpers>

// <vc-spec>
method IsSublist(sub: seq<int>, main: seq<int>) returns (result: bool)
    ensures true <== (exists i :: 0 <= i <= |main| - |sub| && sub == main[i..i + |sub|])
// </vc-spec>
// <vc-code>
{
  result := SublistExists(sub, main);
}
// </vc-code>

