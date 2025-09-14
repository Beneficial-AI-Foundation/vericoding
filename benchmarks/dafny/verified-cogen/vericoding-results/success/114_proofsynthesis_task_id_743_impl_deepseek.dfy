// <vc-preamble>
function RotationSplit(len: int, n: int): int
    requires len > 0
{
    len - (n % len)
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): Removed duplicate function */
// </vc-helpers>

// <vc-spec>
method RotateRight(list: array<int>, n: int) returns (new_list: array<int>)
    requires list.Length > 0
    ensures new_list.Length == list.Length
    ensures fresh(new_list)
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 3): Fixed compilation by removing duplicate function reference */
  var split := list.Length - (n % list.Length);
  new_list := new int[list.Length];
  var i := 0;
  while i < list.Length
      invariant 0 <= i <= list.Length
      invariant forall j :: 0 <= j < i ==> new_list[j] == if j < split then list[list.Length - split + j] else list[j - split]
  {
      if i < split {
          new_list[i] := list[list.Length - split + i];
      } else {
          new_list[i] := list[i - split];
      }
      i := i + 1;
  }
}
// </vc-code>
