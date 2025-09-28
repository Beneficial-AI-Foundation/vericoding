// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method MaxOfList(lst: array<int>) returns (result: int)
    requires lst.Length > 0
    ensures exists i :: 0 <= i < lst.Length && lst[i] == result
    ensures forall i :: 0 <= i < lst.Length ==> lst[i] <= result
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): Added loop invariants to ensure the maximum is correctly found and postconditions hold */
{
  var max := lst[0];
  var i := 1;
  while i < lst.Length
    invariant 1 <= i <= lst.Length
    invariant forall k :: 0 <= k < i ==> lst[k] <= max
    invariant exists k :: 0 <= k < i && lst[k] == max
  {
    if lst[i] > max { max := lst[i]; }
    i := i + 1;
  }
  result := max;
}
// </vc-code>
