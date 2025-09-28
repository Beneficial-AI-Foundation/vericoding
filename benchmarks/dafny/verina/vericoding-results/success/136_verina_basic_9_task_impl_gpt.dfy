// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
predicate ExistsAnyCommon(a: array<int>, b: array<int>) reads a, b {
  exists i:int, j:int :: 0 <= i < a.Length && 0 <= j < b.Length && a[i] == b[j]
}

predicate ExistsFirstI(a: array<int>, b: array<int>, i: int)
  requires 0 <= i <= a.Length
  reads a, b
{
  exists x:int, y:int :: 0 <= x < i && 0 <= y < b.Length && a[x] == b[y]
}

predicate ExistsFirstIJ(a: array<int>, b: array<int>, i: int, j: int)
  requires 0 <= i < a.Length
  requires 0 <= j <= b.Length
  reads a, b
{
  exists x:int, y:int :: 0 <= x < a.Length && 0 <= y < b.Length && (x < i || (x == i && y < j)) && a[x] == b[y]
}
// </vc-helpers>

// <vc-spec>
method HasCommonElement(a: array<int>, b: array<int>) returns (result: bool)
    requires 
        a.Length > 0 &&
        b.Length > 0
    ensures
        result == (exists i, j :: 0 <= i < a.Length && 0 <= j < b.Length && a[i] == b[j])
// </vc-spec>
// <vc-code>
{
  var i := 0;
  result := false;
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant result == (exists x:int, y:int :: 0 <= x < i && 0 <= y < b.Length && a[x] == b[y])
    decreases a.Length - i
  {
    var j := 0;
    while j < b.Length
      invariant 0 <= j <= b.Length
      invariant 0 <= i < a.Length
      invariant result == (exists x:int, y:int :: 0 <= x < a.Length && 0 <= y < b.Length && (x < i || (x == i && y < j)) && a[x] == b[y])
      decreases b.Length - j
    {
      if a[i] == b[j] {
        result := true;
      }
      j := j + 1;
    }
    i := i + 1;
  }
}
// </vc-code>
