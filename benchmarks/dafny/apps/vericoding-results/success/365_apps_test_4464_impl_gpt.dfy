predicate ValidInput(A: int, B: int, C: int)
{
  1 <= A <= 100 && 1 <= B <= 100 && 0 <= C < B
}

predicate IsSolvable(A: int, B: int, C: int)
{
  exists i :: 1 <= i < B && (i * (A % B)) % B == C
}

// <vc-helpers>
lemma ExtendExistsMonotone(n: int, ab: int, B: int, C: int)
  requires 1 <= B
  requires exists j :: 1 <= j < n && (j * ab) % B == C
  ensures exists j :: 1 <= j < n + 1 && (j * ab) % B == C
{
  var k :| 1 <= k < n && (k * ab) % B == C;
  assert exists j :: 1 <= j < n + 1 && (j * ab) % B == C by {
    var j := k;
    assert 1 <= j;
    assert j < n + 1;
    assert (j * ab) % B == C;
  }
}

lemma ExtendExistsRange(n: int, ab: int, B: int, C: int)
  requires 1 <= B
  requires 1 <= n
  requires (n * ab) % B == C
  ensures exists j :: 1 <= j < n + 1 && (j * ab) % B == C
{
  assert exists j :: 1 <= j < n + 1 && (j * ab) % B == C by {
    var j := n;
    assert 1 <= j;
    assert j < n + 1;
    assert (j * ab) % B == C;
  }
}
// </vc-helpers>

// <vc-spec>
method solve(A: int, B: int, C: int) returns (result: string)
  requires ValidInput(A, B, C)
  ensures result == "YES" <==> IsSolvable(A, B, C)
  ensures result == "NO" || result == "YES"
// </vc-spec>
// <vc-code>
{
  var ab := A % B;
  var found := false;
  var i := 1;
  while i < B
    invariant 1 <= i <= B
    invariant found ==> exists j :: 1 <= j < i && ((j * ab) % B) == C
    invariant !found ==> (forall j :: 1 <= j < i ==> ((j * ab) % B) != C)
    decreases B - i
  {
    if ((i * ab) % B) == C {
      found := true;
      ExtendExistsRange(i, ab, B, C);
      i := i + 1;
    } else {
      if found {
        ExtendExistsMonotone(i, ab, B, C);
      } else {
        assert forall j {:trigger ((j * ab) % B)} :: 1 <= j < i + 1 ==> ((j * ab) % B) != C by {
          forall j | 1 <= j < i + 1
            ensures ((j * ab) % B) != C
          {
            if j < i {
              assert ((j * ab) % B) != C;
            } else {
              assert j == i;
              assert ((j * ab) % B) != C;
            }
          }
        }
      }
      i := i + 1;
    }
  }
  assert i == B;
  if found {
    var k :| 1 <= k < i && (k * ab) % B == C;
    assert (k * (A % B)) % B == C;
    assert IsSolvable(A, B, C) by {
      var j := k;
      assert 1 <= j < B;
      assert (j * (A % B)) % B == C;
    }
    result := "YES";
  } else {
    assert forall j {:trigger ((j * (A % B)) % B)} :: 1 <= j < B ==> (j * (A % B)) % B != C by {
      forall j | 1 <= j < B
        ensures (j * (A % B)) % B != C
      {
        assert i == B;
        assert 1 <= j < i;
        assert (j * ab) % B != C;
        assert ab == A % B;
      }
    }
    assert !IsSolvable(A, B, C);
    result := "NO";
  }
}
// </vc-code>

