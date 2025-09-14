function sum(a: array<int>, i: int): int
    requires 0 <= i < a.Length
    reads a
{
    a[i] + if i == 0 then 0 else sum(a, i - 1)
}

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method cumsum(a: array<int>, b: array<int>)
    requires  a.Length == b.Length && a.Length > 0 && a != b
    // when you change a  , that's not the same object than b . 
    //requires b.Length > 0 
    ensures forall i | 0 <= i < a.Length :: b[i] == sum(a, i)
    modifies b
// </vc-spec>
// <vc-code>
{
  var n := a.Length;
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant forall j | 0 <= j < i :: b[j] == sum(a, j)
  {
    if i == 0 {
      b[0] := a[0];
      assert b[0] == sum(a, 0);
    } else {
      b[i] := b[i-1] + a[i];
      assert b[i] == a[i] + b[i-1];
      assert b[i-1] == sum(a, i-1);
      assert sum(a, i) == a[i] + sum(a, i-1);
      assert b[i] == sum(a, i);
    }
    i := i + 1;
  }
}
// </vc-code>

