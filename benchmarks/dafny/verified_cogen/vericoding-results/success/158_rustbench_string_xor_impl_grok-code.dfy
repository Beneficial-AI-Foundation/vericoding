// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

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
/* code modified by LLM (iteration 5): Changed for loop to while loop to fix compilation error with for loop bounds when a.Length==0 */
  result := new char[a.Length];
  var i : int := 0;
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant result.Length == a.Length
    invariant forall k :: 0 <= k < i ==> (result[k] == '0' || result[k] == '1')
    invariant forall k :: 0 <= k < i ==> result[k] == (if a[k] == b[k] then '0' else '1')
  {
    result[i] := if a[i] == b[i] then '0' else '1';
    i := i + 1;
  }
}
// </vc-code>
