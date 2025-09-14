// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function XORChar(a: char, b: char): char
  requires a == '0' || a == '1'
  requires b == '0' || b == '1'
  ensures XORChar(a, b) == '0' || XORChar(a, b) == '1'
  ensures XORChar(a, b) == (if a == b then '0' else '1')
{
  if a == b then '0' else '1'
}
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
  /* code modified by LLM (iteration 3): Fixed result reference in ensures clause */
  var length := a.Length;
  result := new char[length];
  var i := 0;
  
  while i < length
    invariant 0 <= i <= length
    invariant result.Length == length
    invariant forall j :: 0 <= j < i ==> result[j] == '0' || result[j] == '1'
    invariant forall j :: 0 <= j < i ==> result[j] == XORChar(a[j], b[j])
  {
    result[i] := XORChar(a[i], b[i]);
    i := i + 1;
  }
}
// </vc-code>
