// <vc-helpers>
predicate IsEven(n: int)
{
    n % 2 == 0
}

function FindSmallestEvenValue(numbers: seq<int>): int
    requires |numbers| > 0
    requires exists i :: 0 <= i < |numbers| && IsEven(numbers[i])
{
    var evens := seq(i | 0 <= i < |numbers| && IsEven(numbers[i]) | numbers[i]);
    assert |evens| > 0;
    MinSeq(evens)
}

function MinSeq(s: seq<int>): int
    requires |s| > 0
{
    if |s| == 1 then s[0]
    else if s[0] <= MinSeq(s[1..]) then s[0]
    else MinSeq(s[1..])
}

lemma MinSeqProps(s: seq<int>)
    requires |s| > 0
    ensures MinSeq(s) in s
    ensures forall x :: x in s ==> MinSeq(s) <= x
{
    if |s| == 1 {
        return;
    }
    MinSeqProps(s[1..]);
}
// </vc-helpers>

// <vc-description>
/*
function_signature: def pluck(numbers: List[Int]) -> List[Int]
Given an array representing a branch of a tree that has non-negative integer nodes your task is to pluck one of the nodes and return it. The plucked node should be the node with the smallest even value. If multiple nodes with the same smallest even value are found return the node that has smallest index.
*/
// </vc-description>

// <vc-spec>
method Pluck(numbers: seq<int>) returns (result: seq<int>)
    requires forall i :: 0 <= i < |numbers| ==> numbers[i] >= 0
    ensures if (forall i :: 0 <= i < |numbers| ==> !IsEven(numbers[i])) 
            then |result| == 0
            else |result| == 2 && IsEven(result[0]) && 0 <= result[1] < |numbers| &&
                 numbers[result[1]] == result[0] &&
                 (forall i :: 0 <= i < |numbers| && IsEven(numbers[i]) ==> result[0] <= numbers[i]) &&
                 (forall i :: 0 <= i < result[1] && IsEven(numbers[i]) ==> result[0] < numbers[i])
// </vc-spec>
// <vc-code>
{
    var evenIndices := [];
    var i := 0;
    
    while i < |numbers|
        invariant 0 <= i <= |numbers|
        invariant forall j :: j in evenIndices ==> 0 <= j < i && IsEven(numbers[j])
        invariant forall j :: 0 <= j < i && IsEven(numbers[j]) ==> j in evenIndices
    {
        if IsEven(numbers[i]) {
            evenIndices := evenIndices + [i];
        }
        i := i + 1;
    }
    
    if |evenIndices| == 0 {
        result := [];
        return;
    }
    
    var minValue := numbers[evenIndices[0]];
    var minIndex := evenIndices[0];
    i := 1;
    
    while i < |evenIndices|
        invariant 1 <= i <= |evenIndices|
        invariant minIndex in evenIndices[0..i]
        invariant minValue == numbers[minIndex]
        invariant forall j :: j in evenIndices[0..i] ==> minValue <= numbers[j]
        invariant forall j :: j in evenIndices[0..i] && numbers[j] == minValue ==> minIndex <= j
    {
        if numbers[evenIndices[i]] < minValue {
            minValue := numbers[evenIndices[i]];
            minIndex := evenIndices[i];
        }
        i := i + 1;
    }
    
    result := [minValue, minIndex];
}
// </vc-code>
