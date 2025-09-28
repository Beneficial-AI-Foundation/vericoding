// <vc-preamble>
function RotationSplit(len: int, n: int): int
    requires len > 0
{
    len - (n % len)
}
// </vc-preamble>

// <vc-helpers>
function RotIndex(len: int, n: int, i: int): int
    requires len > 0 && 0 <= i < len
{
    (i + RotationSplit(len, n)) % len
}

lemma RotationSplitRange(len: int, n: int)
    requires len > 0
    ensures 1 <= RotationSplit(len, n) <= len
{
}

lemma RotIndexInRange(len: int, n: int, i: int)
    requires len > 0 && 0 <= i < len
    ensures 0 <= RotIndex(len, n, i) < len
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
  var res := new int[len];
  var k := RotationSplit(len, n);
  var i := 0;
  while i < len
    invariant 0 <= i <= len
  {
    var t := (i + k) % len;
    res[t] := list[i];
    i := i + 1;
  }
  new_list := res;
}
// </vc-code>
