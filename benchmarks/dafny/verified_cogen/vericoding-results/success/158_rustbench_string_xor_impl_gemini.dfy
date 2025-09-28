// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function XorChar(c1: char, c2: char): char { if c1 == c2 then '0' else '1' }
// </vc-helpers>

// <vc-spec>
method StringXor(a: array<char>, b: array<char>) returns (result: array<char>)
    requires a.Length == b.Length
    requires forall i :: 0 <= i < a.Length ==> a[i] == '0' || a[i] == '1'
    requires forall i :: 0 <= i < b.Length ==> b[i] == '0' || b[i] == '1'
    ensures result.Length == a.Length
    ensures forall i :: 0 <= i < result.Length ==> (result[i] == '0' || result[i] == '1')
    ensures forall i :: 0 <= i < result.Length ==> result[i] == (if a[i] == b[i] then '0' else '1')
// </vc-spec>
// <vc-code>
{
  result := new char[a.Length];
  var i := 0;
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant result.Length == a.Length
    invariant forall k :: 0 <= k < i ==> result[k] == XorChar(a[k], b[k])
  {
    result[i] := XorChar(a[i], b[i]);
    i := i + 1;
  }
}
// </vc-code>
