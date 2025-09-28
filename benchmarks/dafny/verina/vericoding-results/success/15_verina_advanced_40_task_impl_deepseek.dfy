// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): max function for integer comparison */
function max(a: int, b: int): int { if a > b then a else b }
// </vc-helpers>

// <vc-spec>
method MaxOfList(lst: array<int>) returns (result: int)
    requires lst.Length > 0
    ensures exists i :: 0 <= i < lst.Length && lst[i] == result
    ensures forall i :: 0 <= i < lst.Length ==> lst[i] <= result
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): fixed loop invariant to track current max properly */
{
  result := lst[0];
  var index: int := 1;
  while index < lst.Length
    invariant 0 <= index <= lst.Length
    invariant exists i :: 0 <= i < index && lst[i] == result
    invariant forall i :: 0 <= i < index ==> lst[i] <= result
  {
    result := max(result, lst[index]);
    index := index + 1;
  }
}
// </vc-code>
