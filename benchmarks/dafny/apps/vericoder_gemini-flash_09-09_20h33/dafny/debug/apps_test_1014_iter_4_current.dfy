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
function IntToString(i: int): string
  ensures (i >= 0 && i <= 9) ==> (IntToString(i) == new string(i + '0'))
{
  if i == 0 then "0"
  else if i == 1 then "1"
  else if i == 2 then "2"
  else if i == 3 then "3"
  else if i == 4 then "4"
  else if i == 5 then "5"
  else if i == 6 then "6"
  else if i == 7 then "7"
  else if i == 8 then "8"
  else if i == 9 then "9"
  else 
    var s := "";
    var temp := i;
    while temp > 0 
      invariant temp >= 0;
      invariant forall k :: 0 <= k < |s| && ('0' <= s[k] <= '9'); // all chars are digits
    {
      s := new string([('0' + (temp % 10)) as char]) + s;
      temp := temp / 10;
    }
    s

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
        assert IsWinForWhite(n); // follows from ParityProperty and definition of IsWinForBlack
        var move := OptimalWhiteMove(n);
        result := "white\n" + IntToString(move.0) + " " + IntToString(move.1) + "\n";
    }
}
// </vc-code>

