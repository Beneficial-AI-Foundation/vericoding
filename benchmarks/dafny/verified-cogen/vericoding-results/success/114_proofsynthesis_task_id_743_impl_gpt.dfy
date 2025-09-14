// <vc-preamble>
function RotationSplit(len: int, n: int): int
    requires len > 0
{
    len - (n % len)
}
// </vc-preamble>

// <vc-helpers>
function RightIndex(i: int, len: int, r: int): int
    requires len > 0
    requires 0 <= i < len
    requires 0 <= r < len
{
    if i + len - r >= len then i - r else i + len - r
}

lemma RightIndexRange(i: int, len: int, r: int)
    requires len > 0
    requires 0 <= i < len
    requires 0 <= r < len
    ensures 0 <= RightIndex(i, len, r) < len
{
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
  var newArr := new int[len];
  var r := n % len;
  var i := 0;
  while i < len
    invariant 0 <= i <= len
    invariant newArr.Length == len
    decreases len - i
  {
    var j := i + len - r;
    if j >= len {
      j := j - len;
    }
    assert 0 <= j < len;
    newArr[i] := list[j];
    i := i + 1;
  }
  new_list := newArr;
}
// </vc-code>
