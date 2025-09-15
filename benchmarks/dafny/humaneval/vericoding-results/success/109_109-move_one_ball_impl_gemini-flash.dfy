// <vc-preamble>
function is_sorted(a: seq<int>) : bool {
  forall i, j :: 0 <= i < j < |a| ==> a[i] <= a[j]
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): Removed by LLM, as it was not needed for correctness or verification within the current implementation. */
// </vc-helpers>

// <vc-spec>
method move_one_ball(a: seq<int>) returns (can: bool)

  requires |a| > 0
  requires forall i, j :: 0 <= i < |a| && 0 <= j < |a| && i != j ==> a[i] != a[j]

  ensures can <==> exists i :: 0 <= i < |a| && is_sorted(a[i..] + a[..i])
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 4): The problem statement requires showing that by moving *one* specific ball (which effectively means rotating the array), we can achieve a sorted sequence. The original approach was to check if *any* rotation was sorted. This iterative refinement makes 'can' reflect this. */
{
  can := false;
  var i := 0;
  while i < |a|
    invariant 0 <= i <= |a|
    invariant can == (exists j :: 0 <= j < i && is_sorted(a[j..] + a[..j]))
  {
    if is_sorted(a[i..] + a[..i])
    {
      can := true;
    }
    i := i + 1;
  }
}
// </vc-code>
