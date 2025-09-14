// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): [no helpers needed] */

// </vc-helpers>

// <vc-spec>
method flip (a: array<int>, num: int)
requires a.Length > 0;
requires 0 <= num < a.Length;
modifies a;
ensures forall k :: 0 <= k <= num ==> a[k] == old(a[num-k])
ensures forall k :: num < k < a.Length ==> a[k] == old(a[k])
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 5): [Removed redundant invariant on a.Length that caused a compilation warning.] */
  var i := 0;
  var j := num;
  while (i < j)
    modifies a
    invariant 0 <= i <= (num + 1) / 2
    invariant j == num - i
    invariant forall k :: 0 <= k < i ==> a[k] == old(a[num - k])
    invariant forall k :: j < k <= num ==> a[k] == old(a[num - k])
    invariant forall k :: i <= k <= j ==> a[k] == old(a[k])
    invariant forall k :: num < k < a.Length ==> a[k] == old(a[k])
  {
    a[i], a[j] := a[j], a[i];
    i := i + 1;
    j := j - 1;
  }
}
// </vc-code>
