// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): add reads frame and index range guard for j */
predicate AllAfterNotElem(a: array<int>, elem: int, i: int) reads a { forall j :: 0 <= j < a.Length && i < j ==> a[j] != elem }
// </vc-helpers>

// <vc-spec>
method LastPosition(a: array<int>, elem: int) returns (result: int)
    requires 0 < a.Length < 100_000
    requires exists i :: 0 <= i < a.Length && a[i] == elem
    ensures 0 <= result < a.Length
    ensures forall i :: result < i < a.Length ==> a[i] != elem
    ensures a[result] == elem
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): backward scan to find last occurrence; added invariant with in-bounds guard and proof that i cannot be negative using a witness */
  var i := a.Length - 1;
  var k :| 0 <= k < a.Length && a[k] == elem;
  while 0 <= i && a[i] != elem
    invariant -1 <= i < a.Length
    invariant forall j :: 0 <= j < a.Length && i < j ==> a[j] != elem
    decreases i + 1
  {
    i := i - 1;
  }
  // After loop, not (0 <= i && a[i] != elem)
  if i < 0 {
    assert 0 <= k < a.Length && i < k;
    assert a[k] != elem; // from the invariant with j = k, since i < 0 implies i < k
    assert false;
  }
  assert !(0 <= i && a[i] != elem);
  assert i >= 0;
  assert a[i] == elem;
  result := i;
}

// </vc-code>
