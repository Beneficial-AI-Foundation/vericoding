predicate ValidInput(input: seq<string>)
{
    |input| == 8 &&
    (forall i :: 0 <= i < 8 ==> |input[i]| == 8) &&
    (forall i, j :: 0 <= i < 8 && 0 <= j < 8 ==> input[i][j] in {'W', 'B'})
}

predicate HasAlternatingRow(row: string)
    requires |row| == 8
    requires forall j :: 0 <= j < 8 ==> row[j] in {'W', 'B'}
{
    forall k :: 1 <= k < 8 ==> row[k] != row[k-1]
}

predicate AllRowsHaveAlternatingPattern(input: seq<string>)
    requires ValidInput(input)
{
    forall i :: 0 <= i < 8 ==> HasAlternatingRow(input[i])
}

// <vc-helpers>
lemma AlternatingRowPattern(row: string)
    requires |row| == 8
    requires forall j :: 0 <= j < 8 ==> row[j] in {'W', 'B'}
    ensures HasAlternatingRow(row) <==> (forall k :: 0 <= k < 8 ==> row[k] == if k % 2 == 0 then row[0] else if row[0] == 'W' then 'B' else 'W')
{
}

lemma ValidInputImpliesAllRowsLength8(input: seq<string>)
    requires ValidInput(input)
    ensures forall i :: 0 <= i < 8 ==> |input[i]| == 8
{
}

lemma FirstCharacterDeterminesPattern(row: string)
    requires |row| == 8
    requires forall j :: 0 <= j < 8 ==> row[j] in {'W', 'B'}
    requires HasAlternatingRow(row)
    ensures row[0] == 'W' ==> row == "WBWBWBWB"
    ensures row[0] == 'B' ==> row == "BWBWBWBW"
{
    var pattern1 := "WBWBWBWB";
    var pattern2 := "BWBWBWBW";
    
    assert forall k :: 0 <= k < 8 ==> 
        if row[0] == 'W' then row[k] == pattern1[k] else row[k] == pattern2[k];
}
// </vc-helpers>

// <vc-spec>
method solve(input: seq<string>) returns (result: string)
    requires ValidInput(input)
    ensures result in
// </vc-spec>
// <vc-code>
{
    var expected1 := "WBWBWBWB";
    var expected2 := "BWBWBWBW";
    
    if AllRowsHaveAlternatingPattern(input) {
        if input[0][0] == 'W' {
            result := expected1;
        } else {
            result := expected2;
        }
    } else {
        result := "No solution exists";
    }
}
// </vc-code>

