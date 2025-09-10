predicate ValidInput(n: int, rows: seq<string>)
{
    n >= 0 && |rows| == n && forall i :: 0 <= i < |rows| ==> |rows[i]| == 5
}

predicate HasAdjacentEmptySeats(rows: seq<string>)
{
    exists i :: 0 <= i < |rows| && 
        ((|rows[i]| >= 2 && rows[i][0] == 'O' && rows[i][1] == 'O') ||
         (|rows[i]| >= 5 && rows[i][3] == 'O' && rows[i][4] == 'O'))
}

predicate NoAdjacentEmptySeats(rows: seq<string>)
{
    forall i :: 0 <= i < |rows| ==> 
        !((|rows[i]| >= 2 && rows[i][0] == 'O' && rows[i][1] == 'O') ||
          (|rows[i]| >= 5 && rows[i][3] == 'O' && rows[i][4] == 'O'))
}

predicate ValidSolution(result: string, rows: seq<string>)
{
    result != "NO" ==> |result| >= 4
}

// <vc-helpers>
function Digit(n: int): char
  requires 0 <= n < 10
{
  if n == 0 then '0'
  else if n == 1 then '1'
  else if n == 2 then '2'
  else if n == 3 then '3'
  else if n == 4 then '4'
  else if n == 5 then '5'
  else if n == 6 then '6'
  else if n == 7 then '7'
  else if n == 8 then '8'
  else '9'
}

function IntToString(n: int): seq<char>
  requires n >= 0
{
  if n == 0 then ['0']
  else
    IntToString(n / 10) + [Digit(n % 10)]
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, rows: seq<string>) returns (result: string)
    requires ValidInput(n, rows)
    ensures result == "NO" || |result| >= 4
    ensures result == "NO" ==> NoAdjacentEmptySeats(rows)
    ensures result != "NO" ==> HasAdjacentEmptySeats(rows)
    ensures ValidSolution(result, rows)
// </vc-spec>
// <vc-code>
{
    var i := 0;
    while i < |rows|
      invariant forall j :: 0 <= j < i ==> !((|rows[j]| >= 2 && rows[j][0] == 'O' && rows[j][1] == 'O') ||
                                                (|rows[j]| >= 5 && rows[j][3] == 'O' && rows[j][4] == 'O'))
    {
        var row := rows[i];
        if (|row| >= 2 && row[0] == 'O' && row[1] == 'O'){
            result := "Row " + IntToString(i) + " Seats 1 2";
            return;
        } else if (|row| >= 5 && row[3] == 'O' && row[4] == 'O') {
            result := "Row " + IntToString(i) + " Seats 4 5";
            return;
        }
        i := i + 1;
    }
    result := "NO";
}
// </vc-code>

