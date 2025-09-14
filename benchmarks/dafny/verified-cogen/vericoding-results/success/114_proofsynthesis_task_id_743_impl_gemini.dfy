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
  var len := list.Length;
  new_list := new int[len];

  var split_point := RotationSplit(len, n);

  // The length of the part that moves to the front
  var k := len - split_point;

  // Copy the end part of 'list' to the start of 'new_list'
  var i := 0;
  while i < k
    invariant 0 <= i <= k
    invariant new_list.Length == len
  {
    new_list[i] := list[split_point + i];
    i := i + 1;
  }

  // Copy the start part of 'list' to the end of 'new_list'
  var j := 0;
  while j < split_point
    invariant 0 <= j <= split_point
    invariant new_list.Length == len
  {
    new_list[k + j] := list[j];
    j := j + 1;
  }
}
// </vc-code>
