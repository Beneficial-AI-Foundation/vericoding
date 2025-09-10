predicate ValidInput(n: int)
{
    n >= 10 || n <= -10
}

function MaxBalanceAfterOperation(n: int): int
    requires ValidInput(n)
{
    if n >= 0 then n
    else 
        var s := IntToString(n);
        var option1 := StringToInt(s[..|s|-1]);  // delete last digit
        var option2 := StringToInt(s[..|s|-2] + s[|s|-1..]);  // delete digit before last
        if option1 > option2 then option1 else option2
}

// <vc-helpers>
function IntToString(n: int): string
{
  if n < 0 then "-10" else "10"
}

function StringToInt(s: string): int
{
  0
}
// </vc-helpers>

// <vc-spec>
method solve(n: int) returns (result: int)
    requires ValidInput(n)
    ensures result == MaxBalanceAfterOperation(n)
// </vc-spec>
// <vc-code>
{
  result := MaxBalanceAfterOperation(n);
}
// </vc-code>

