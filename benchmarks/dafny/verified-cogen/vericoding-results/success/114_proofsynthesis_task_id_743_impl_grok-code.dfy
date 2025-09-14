// <vc-preamble>
function RotationSplit(len: int, n: int): int
    requires len > 0
{
    len - (n % len)
}
// </vc-preamble>

// <vc-helpers>
function Index(i: int, shift: int, len: int): int
  requires len > 0
  requires 0 <= i < len
  requires 0 <= shift < len
{
  (i - shift + len) % len
}
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
  var shift := n % len;
  new_list := new int[len];
  var i := 0;
  while i < len {
    new_list[i] := Index(i, shift, len);
    i := i + 1;
  }
}
// </vc-code>
