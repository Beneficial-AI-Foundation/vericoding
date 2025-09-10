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
// IntToString and StringToInt are assumed to be defined or built-in.
// ValidInput ensures |n| >= 10 for negative n, so string length >= 3, avoiding out-of-bounds issues in slicing.
// </vc-helpers>

// <vc-spec>
method solve(n: int) returns (result: int)
    requires ValidInput(n)
    ensures result == MaxBalanceAfterOperation(n)
// </vc-spec>
// <vc-code>
{
  if n >= 0 {
    return n;
  } else {
    var s := IntToString(n);
    var option1 := StringToInt(s[..|s|-1]);
    var option2 := StringToInt(s[..|s|-2] + s[|s|-1..]);
    if option1 > option2 {
      return option1;
    } else {
      return option2;
    }
  }
}
// </vc-code>

