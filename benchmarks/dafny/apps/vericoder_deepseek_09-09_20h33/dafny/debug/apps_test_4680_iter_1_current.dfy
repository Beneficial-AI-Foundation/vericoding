predicate ValidInput(A: int, B: int, C: int)
{
    1 <= A <= 10 && 1 <= B <= 10 && 1 <= C <= 10
}

predicate CanFormHaiku(A: int, B: int, C: int)
{
    (A == 5 && B == 5 && C == 7) ||
    (A == 5 && B == 7 && C == 5) ||
    (A == 7 && B == 5 && C == 5)
}

predicate ValidOutput(result: string)
{
    result in {"YES", "NO"}
}

// <vc-helpers>
lemma Count575(a: int, b: int, c: int)
    requires ValidInput(a, b, c)
    ensures (a == 5 && b == 5 && c == 7) ||
            (a == 5 && b == 7 && c == 5) ||
            (a == 7 && b == 5 && c == 5) <==> 
            (a + b + c == 17) && (a == 5 || a == 7) && (b == 5 || b == 7) && (c == 5 || c == 7)
{
}
// </vc-helpers>

// <vc-spec>
method solve(A: int, B: int, C: int) returns (result: string)
    requires ValidInput(A, B, C)
    ensures ValidOutput(result)
    ensures result == "YES" <==> CanFormHaiku(A, B, C)
// </vc-spec>
// <vc-code>
{
  Count575(A, B, C);
  
  var total := A + B + C;
  if total == 17 && ((A == 5 || A == 7) && (B == 5 || B == 7) && (C == 5 || C == 7)) then {
    result := "YES";
  } else {
    result := "NO";
  }
}
// </vc-code>

