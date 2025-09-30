// <vc-preamble>
function RotationSplit(len: int, n: int): int
    requires len > 0
{
    len - (n % len)
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method RotateRight(list: array<int>, n: int) returns (new_list: array<int>)
    requires list.Length > 0
    ensures new_list.Length == list.Length
    ensures fresh(new_list)
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): Fixed array initialization syntax */
  var len := list.Length;
  new_list := new int[len];
  var split := RotationSplit(len, n);
  var i := 0;
  while i < len
    invariant 0 <= i <= len
    invariant forall j :: 0 <= j < i ==> new_list[j] == list[(split + j) % len]
  {
    new_list[i] := list[(split + i) % len];
    i := i + 1;
  }
}
// </vc-code>
