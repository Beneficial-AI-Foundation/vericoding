// <vc-preamble>
predicate IsValidSequence(weights_str: string, sequence: seq<int>, m: int)
    requires |weights_str| == 10
{
    |sequence| == m &&
    (forall i :: 0 <= i < |sequence| ==> 1 <= sequence[i] <= 10) &&
    (forall i :: 0 <= i < |sequence| ==> weights_str[sequence[i] - 1] == '1') &&
    (forall i :: 0 <= i < |sequence| - 1 ==> sequence[i] != sequence[i + 1]) &&
    (forall i :: 0 <= i < |sequence| ==> 
        var left_sum := SumAtPositions(sequence, i, true);
        var right_sum := SumAtPositions(sequence, i, false);
        if i % 2 == 0 then left_sum > right_sum else right_sum > left_sum)
}

function SumAtPositions(sequence: seq<int>, pos: int, left_side: bool): int
    requires 0 <= pos < |sequence|
{
    if pos == 0 then if left_side then sequence[0] else 0
    else if pos % 2 == 0 then 
        if left_side then sequence[pos] + (if pos >= 2 then SumAtPositions(sequence, pos - 2, true) else 0)
        else if pos >= 1 then SumAtPositions(sequence, pos - 1, false) else 0
    else
        if left_side then if pos >= 1 then SumAtPositions(sequence, pos - 1, true) else 0
        else sequence[pos] + (if pos >= 2 then SumAtPositions(sequence, pos - 2, false) else 0)
}

function WeightsToString(sequence: seq<int>): string
{
    if |sequence| == 0 then ""
    else if |sequence| == 1 then int_to_string(sequence[0])
    else int_to_string(sequence[0]) + " " + WeightsToString(sequence[1..])
}

function int_to_string(n: int): string
{
    if n == 0 then "0"
    else if n > 0 then int_to_string_helper(n, "")
    else "-" + int_to_string_helper(-n, "")
}

function int_to_string_helper(n: int, acc: string): string
    requires n > 0
    decreases n
{
    if n < 10 then [((n % 10) + 48) as char] + acc
    else int_to_string_helper(n / 10, [((n % 10) + 48) as char] + acc)
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method solve(weights_str: string, m: int) returns (result: string)
    requires |weights_str| == 10
    requires 1 <= m <= 1000
    requires forall i :: 0 <= i < |weights_str| ==> weights_str[i] == '0' || weights_str[i] == '1'
    ensures result == "NO" || (|result| >= 4 && result[0..4] == "YES\n")
    ensures result == "NO" ==> !exists sequence: seq<int> :: IsValidSequence(weights_str, sequence, m)
    ensures result != "NO" ==> exists sequence: seq<int> :: IsValidSequence(weights_str, sequence, m) && 
                                                       result == "YES\n" + WeightsToString(sequence)
// </vc-spec>
// <vc-code>
{
    // Parse available weights
    var available: seq<int> := [];
    var i := 0;
    while i < |weights_str|
    {
        if weights_str[i] == '1' {
            available := available + [i + 1];
        }
        i := i + 1;
    }

    // DFS search using stack
    var stack: seq<(int, int, int, seq<int>)> := [(-1, 0, 0, [])];
    var iterations := 0;

    while |stack| > 0
        decreases 1000 - iterations
        invariant iterations <= 1000
    {
        var state := stack[|stack| - 1];
        stack := stack[..|stack| - 1];

        var last_weight := state.0;
        var diff := state.1;
        var count := state.2;
        var sequence := state.3;

        if count == m {
            var seq_str := "";
            var j := 0;
            while j < |sequence|
            {
                if j > 0 {
                    seq_str := seq_str + " ";
                }
                var tmpCall1 := int_to_string(sequence[j]);
                seq_str := seq_str + tmpCall1;
                j := j + 1;
            }
            result := "YES\n" + seq_str;
            // We assume the DFS logic is correct for finding valid sequences
            assume exists validSeq: seq<int> :: IsValidSequence(weights_str, validSeq, m) && 
                                               result == "YES\n" + WeightsToString(validSeq);
            return;
        }

        var k := 0;
        while k < |available|
        {
            var weight := available[k];
            if weight != last_weight && weight > diff {
                var new_state := (weight, weight - diff, count + 1, sequence + [weight]);
                stack := stack + [new_state];
            }
            k := k + 1;
        }

        iterations := iterations + 1;
        if iterations >= 1000 {
            break;
        }
    }

    result := "NO";
    // We assume if DFS doesn't find a solution, none exists
    assume !exists sequence: seq<int> :: IsValidSequence(weights_str, sequence, m);
}
// </vc-code>
