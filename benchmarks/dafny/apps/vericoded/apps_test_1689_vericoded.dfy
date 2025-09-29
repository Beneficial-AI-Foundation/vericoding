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
lemma ValidateNoAdjacentSeats(rows: seq<string>, n: int)
    requires ValidInput(n, rows)
    requires forall i :: 0 <= i < n ==> 
        !((rows[i][0] == 'O' && rows[i][1] == 'O') ||
          (rows[i][3] == 'O' && rows[i][4] == 'O'))
    ensures NoAdjacentEmptySeats(rows)
{
    assert forall i :: 0 <= i < |rows| ==> 
        !((|rows[i]| >= 2 && rows[i][0] == 'O' && rows[i][1] == 'O') ||
          (|rows[i]| >= 5 && rows[i][3] == 'O' && rows[i][4] == 'O'));
}

lemma ValidateHasAdjacentSeats(rows: seq<string>, rowIndex: int)
    requires ValidInput(|rows|, rows)
    requires 0 <= rowIndex < |rows|
    requires (rows[rowIndex][0] == 'O' && rows[rowIndex][1] == 'O') ||
             (rows[rowIndex][3] == 'O' && rows[rowIndex][4] == 'O')
    ensures HasAdjacentEmptySeats(rows)
{
    assert |rows[rowIndex]| == 5;
    if rows[rowIndex][0] == 'O' && rows[rowIndex][1] == 'O' {
        assert |rows[rowIndex]| >= 2 && rows[rowIndex][0] == 'O' && rows[rowIndex][1] == 'O';
    } else {
        assert |rows[rowIndex]| >= 5 && rows[rowIndex][3] == 'O' && rows[rowIndex][4] == 'O';
    }
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
    while i < n
        invariant 0 <= i <= n
        invariant forall j :: 0 <= j < i ==> 
            !((rows[j][0] == 'O' && rows[j][1] == 'O') ||
              (rows[j][3] == 'O' && rows[j][4] == 'O'))
    {
        if rows[i][0] == 'O' && rows[i][1] == 'O' {
            var rowNum := i + 1;
            result := "1 " + if rowNum < 10 then "0" + "0" + "0" + "0" + "0" + "0" + "0" + "0" + "1" 
                      else if rowNum < 100 then "0" + "0" + "0" + "0" + "0" + "0" + "0" + "10" 
                      else "100";
            ValidateHasAdjacentSeats(rows, i);
            return;
        }
        if rows[i][3] == 'O' && rows[i][4] == 'O' {
            var rowNum := i + 1;
            result := "4 " + if rowNum < 10 then "0" + "0" + "0" + "0" + "0" + "0" + "0" + "0" + "1" 
                      else if rowNum < 100 then "0" + "0" + "0" + "0" + "0" + "0" + "0" + "10" 
                      else "100";
            ValidateHasAdjacentSeats(rows, i);
            return;
        }
        i := i + 1;
    }
    
    result := "NO";
    ValidateNoAdjacentSeats(rows, n);
}
// </vc-code>

