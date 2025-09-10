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
lemma AlternatingRowCheck(row: string)
    requires |row| == 8
    requires forall j :: 0 <= j < 8 ==> row[j] in {'W', 'B'}
    ensures HasAlternatingRow(row) <==> (forall k :: 1 <= k < 8 ==> row[k] != row[k-1])
{
    // This lemma just restates the definition for clarity
}
// </vc-helpers>

// <vc-spec>
method solve(input: seq<string>) returns (result: string)
    requires ValidInput(input)
    ensures result in
// </vc-spec>
// <vc-code>
{
    var allAlternating := true;
    var i := 0;
    
    while i < 8
        invariant 0 <= i <= 8
        invariant allAlternating <==> (forall idx :: 0 <= idx < i ==> HasAlternatingRow(input[idx]))
    {
        var j := 1;
        var rowAlternating := true;
        
        while j < 8
            invariant 1 <= j <= 8
            invariant rowAlternating <==> (forall k :: 1 <= k < j ==> input[i][k] != input[i][k-1])
        {
            if input[i][j] == input[i][j-1] {
                rowAlternating := false;
            }
            j := j + 1;
        }
        
        if !rowAlternating {
            allAlternating := false;
        }
        i := i + 1;
    }
    
    if allAlternating {
        result := "Yes";
    } else {
        result := "No";
    }
}
// </vc-code>

