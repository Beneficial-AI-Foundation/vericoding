predicate ValidInput(n: int) {
    n >= 2
}

predicate IsWinForWhite(n: int) {
    n % 2 == 0
}

predicate IsWinForBlack(n: int) {
    n % 2 == 1
}

function OptimalWhiteMove(n: int): (int, int)
    requires ValidInput(n)
    requires IsWinForWhite(n)
{
    (1, 2)
}

predicate ValidResult(n: int, result: string) 
    requires ValidInput(n)
{
    if IsWinForBlack(n) then
        result == "black\n"
    else
        result == "white\n1 2\n"
}

// <vc-helpers>
lemma ParityProperty(n: int)
  ensures (n % 2 == 0 && n % 2 == 1) == false
{}

// Helper function to convert an integer to its string representation.
function IntToString(i: int): string
  requires i >= 0
  ensures (i == 0) ==> (IntToString(i) == "0")
  ensures (i > 0 && i <= 9) ==> (IntToString(i) == new string([('0' + i) as char]))
{
  if i == 0 then "0"
  else if i > 0 && i <= 9 then new string([('0' + i) as char])
  else  // For i > 9, convert by repeatedly taking modulo and dividing by 10.
  (
    var s := "";
    var temp := i;
    while temp > 0
      invariant temp >= 0
      invariant forall k :: 0 <= k < |s| && '0' <= s[k] <= '9' // All chars in s are digits
      invariant temp == 0 || s != "" // If temp > 0, s must contain digits
      decreases temp
    {
      s := new string([('0' + (temp % 10)) as char]) + s;
      temp := temp / 10;
    }
    s
  )
}
// </vc-helpers>

// <vc-spec>
method solve(n: int) returns (result: string)
    requires ValidInput(n)
    ensures ValidResult(n, result)
// </vc-spec>
// <vc-code>
{
    if IsWinForBlack(n) {
        result := "black\n";
    } else {
        assert ParityProperty(n); // Proves that IsWinForBlack(n) is false and IsWinForWhite(n) is true
        assert IsWinForWhite(n);
        var move := OptimalWhiteMove(n);
        result := "white\n" + IntToString(move.0) + " " + IntToString(move.1) + "\n";
    }
}
// </vc-code>

