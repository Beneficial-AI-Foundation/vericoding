

// <vc-helpers>
lemma mod_lemma(x: int, y: int)
  requires y != 0
  ensures x % y == if y > 0 then x % y else -(-x % -y)
{
  if y > 0 {
    // Trivial case when y is positive
  } else {
    // When y is negative, use the mathematical property of modulo
    assert -y > 0;
    var pos_mod := (-x) % (-y);
    assert x % y == -pos_mod;
  }
}
// </vc-helpers>

// <vc-spec>
method ElementWiseModulo(a: array<int>, b: array<int>) returns (result: array<int>)
    requires a != null && b != null
    requires a.Length == b.Length
    requires forall i :: 0 <= i < b.Length ==> b[i] != 0
    ensures result != null
    ensures result.Length == a.Length
    ensures forall i :: 0 <= i < result.Length ==> result[i] == a[i] % b[i]
// </vc-spec>
// <vc-code>
{
  result := new int[a.Length];
  var index := 0;
  while index < a.Length
    invariant 0 <= index <= a.Length
    invariant result.Length == a.Length
    invariant forall j :: 0 <= j < index ==> result[j] == a[j] % b[j]
  {
    mod_lemma(a[index], b[index]);
    result[index] := a[index] % b[index];
    index := index + 1;
  }
}
// </vc-code>

