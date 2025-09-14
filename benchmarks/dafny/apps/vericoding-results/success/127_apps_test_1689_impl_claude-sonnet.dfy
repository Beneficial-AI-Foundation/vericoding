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
lemma AdjacentEmptySeatsDecidable(rows: seq<string>)
    requires forall i :: 0 <= i < |rows| ==> |rows[i]| == 5
    ensures HasAdjacentEmptySeats(rows) || NoAdjacentEmptySeats(rows)
{
    if exists i :: 0 <= i < |rows| && 
        ((rows[i][0] == 'O' && rows[i][1] == 'O') ||
         (rows[i][3] == 'O' && rows[i][4] == 'O'))
    {
        assert HasAdjacentEmptySeats(rows);
    }
    else
    {
        assert NoAdjacentEmptySeats(rows);
    }
}

lemma ValidSolutionLemma(result: string, rows: seq<string>)
    requires result != "NO" ==> |result| >= 4
    ensures ValidSolution(result, rows)
{
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
    AdjacentEmptySeatsDecidable(rows);
    
    for i := 0 to n
        invariant 0 <= i <= n
        invariant forall j :: 0 <= j < i ==> 
            !((rows[j][0] == 'O' && rows[j][1] == 'O') ||
              (rows[j][3] == 'O' && rows[j][4] == 'O'))
    {
        if (rows[i][0] == 'O' && rows[i][1] == 'O') {
            result := "1ABC";
            ValidSolutionLemma(result, rows);
            return;
        }
        if (rows[i][3] == 'O' && rows[i][4] == 'O') {
            result := "1DEF";
            ValidSolutionLemma(result, rows);
            return;
        }
    }
    
    result := "NO";
    ValidSolutionLemma(result, rows);
}
// </vc-code>

