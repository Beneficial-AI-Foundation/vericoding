// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function SmallestLength(l: array<array<int>>, upto: int): int
  requires l.Length > 0
  requires 1 <= upto <= l.Length
  reads l
  ensures SmallestLength(l, upto) >= 0
  ensures forall k :: 0 <= k < upto ==> SmallestLength(l, upto) <= l[k].Length
  ensures exists k :: 0 <= k < upto && SmallestLength(l, upto) == l[k].Length
{
  if upto == 1 then
    l[0].Length
  else
    var prev_min := SmallestLength(l, upto - 1);
    if l[upto - 1].Length < prev_min then l[upto - 1].Length else prev_min
}
// </vc-helpers>

// <vc-spec>
method SmallestListLength(list: array<array<int>>) returns (min: int)
    requires list.Length > 0
    ensures min >= 0
    ensures forall i :: 0 <= i < list.Length ==> min <= list[i].Length
    ensures exists i :: 0 <= i < list.Length && min == list[i].Length
// </vc-spec>
// <vc-code>
{
  min := list[0].Length;
  var i := 1;
  while i < list.Length
    invariant 1 <= i <= list.Length
    invariant min == SmallestLength(list, i)
  {
    if list[i].Length < min {
      min := list[i].Length;
    }
    i := i + 1;
  }
}
// </vc-code>
