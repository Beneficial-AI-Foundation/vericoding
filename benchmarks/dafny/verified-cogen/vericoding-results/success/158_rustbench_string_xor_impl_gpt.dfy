// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): retained IsBit predicate for bit validation */
predicate IsBit(c: char) { c == '0' || c == '1' }
/* helper modified by LLM (iteration 3): XorChar returns '0' when equal, '1' otherwise, and ensures the result is a bit */
function XorChar(c1: char, c2: char): char
  ensures IsBit(XorChar(c1, c2))
{
  if c1 == c2 then '0' else '1'
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
  /* code modified by LLM (iteration 3): fixed loop invariant to avoid null comparison and implemented XOR loop */
  result := new char[a.Length];
  var i := 0;
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant result.Length == a.Length
    invariant forall j :: 0 <= j < i ==> result[j] == (if a[j] == b[j] then '0' else '1')
    invariant forall j :: 0 <= j < i ==> (result[j] == '0' || result[j] == '1')
    decreases a.Length - i
  {
    result[i] := if a[i] == b[i] then '0' else '1';
    i := i + 1;
  }
}
// </vc-code>
