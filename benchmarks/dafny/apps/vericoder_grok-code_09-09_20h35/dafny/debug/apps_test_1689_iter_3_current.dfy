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
  match n {
    case 0 => '0'
    case 1 => '1'
    case 2 => '2'
    case 3 => '3'
    case 4 => '4'
    case 5 => '5'
    case 6 => '6'
    case 7 => '7'
    case 8 => '8'
    case 9 => '9'
  }
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
    for i := 0 to |rows| - 1 {
        var row := rows[i];
        if (|row| >= 2 && row[0] == 'O' && row[1] == 'O'){
            result := "Row " + IntToString(i) + " Seats 1 2";
            return;
        } else if (|row| >= 5 && row[3] == 'O' && row[4] == 'O') {
            result := "Row " + IntToString(i) + " Seats 4 5";
            return;
        }
    }
    result := "NO";
}
// </vc-code>

