predicate ValidInput(A: int, B: int, C: int)
{
  1 <= A <= 100 && 1 <= B <= 100 && 0 <= C < B
}

predicate IsSolvable(A: int, B: int, C: int)
{
  exists i :: 1 <= i < B && (i * (A % B)) % B == C
}

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method solve(A: int, B: int, C: int) returns (result: string)
  requires ValidInput(A, B, C)
  ensures result == "YES" <==> IsSolvable(A, B, C)
  ensures result == "NO" || result == "YES"
// </vc-spec>
// <vc-code>
{
  var i := 1;
  while i < B
    invariant 1 <= i <= B
    invariant forall j :: 1 <= j < i ==> (j * (A % B)) % B != C
  {
    if (i * (A % B)) % B == C {
      return "YES";
    }
    i := i + 1;
  }
  return "NO";
}
// </vc-code>

