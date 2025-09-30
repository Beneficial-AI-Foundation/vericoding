predicate ValidInput(A: int, B: int, C: int)
{
  1 <= A <= 100 && 1 <= B <= 100 && 0 <= C < B
}

predicate IsSolvable(A: int, B: int, C: int)
{
  exists i :: 1 <= i < B && (i * (A % B)) % B == C
}

// <vc-helpers>
// (No helper code needed)
// </vc-helpers>

// <vc-spec>
method solve(A: int, B: int, C: int) returns (result: string)
  requires ValidInput(A, B, C)
  ensures result == "YES" <==> IsSolvable(A, B, C)
  ensures result == "NO" || result == "YES"
// </vc-spec>
// <vc-code>
{
  var a := A % B;
  var i := 1;
  while i < B
    invariant 1 <= i <= B
    invariant forall j :: 1 <= j < i ==> (j * a) % B != C
  {
    if (i * a) % B == C {
      // witness for the existential in the postcondition
      assert 1 <= i < B;
      assert (i * a) % B == C;
      assert exists k :: 1 <= k < B && (k * a) % B == C;
      return "YES";
    }
    i := i + 1;
  }
  // by the loop invariant at i == B, no such j in 1..B-1 exists
  assert forall j :: 1 <= j < B ==> (j * a) % B != C;
  return "NO";
}
// </vc-code>

