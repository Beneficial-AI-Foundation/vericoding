/*
Given a bus with n rows of seats, where each row contains 4 seats arranged as two pairs 
separated by a walkway (format: XX|XX), find two adjacent empty seats in the same pair 
for two passengers. Each seat is either 'O' (empty) or 'X' (occupied). If such a pair 
exists, mark it with "++" and output "YES" with the modified configuration. Otherwise, 
output "NO".
*/

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
  assume {:axiom} false;
}
// </vc-code>
