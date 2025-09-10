predicate ValidInput(n: int, numbers: seq<int>)
{
    n >= 3 && n % 3 == 0 &&
    |numbers| == n &&
    forall i :: 0 <= i < |numbers| ==> 1 <= numbers[i] <= 7
}

predicate ValidTriplet(triplet: seq<int>)
{
    |triplet| == 3 &&
    triplet[0] < triplet[1] < triplet[2] &&
    triplet[0] > 0 && triplet[1] > 0 && triplet[2] > 0 &&
    triplet[1] % triplet[0] == 0 && triplet[2] % triplet[1] == 0
}

function FlattenPartition(result: seq<seq<int>>): seq<int>
{
    if |result| == 0 then [] else
    result[0] + FlattenPartition(result[1..])
}

predicate ValidPartition(result: seq<seq<int>>, numbers: seq<int>)
{
    |result| == |numbers| / 3 &&
    (forall i :: 0 <= i < |result| ==> ValidTriplet(result[i])) &&
    multiset(numbers) == multiset(FlattenPartition(result))
}

predicate NoPartitionExists(result: seq<seq<int>>)
{
    |result| == 0
}

// <vc-helpers>
function method CanFormTriplet(a: int, b: int, c: int): bool
{
    a < b < c && a > 0 && b > 0 && c > 0 && b % a == 0 && c % b == 0
}

function method FindTriplets(numbers: seq<int>): seq<seq<int>>
{
    var triplets := [];
    var i := 0;
    while i < |numbers|
        invariant 0 <= i <= |numbers|
    {
        var j := i + 1;
        while j < |numbers|
            invariant i < j <= |numbers|
        {
            var k := j + 1;
            while k < |numbers|
                invariant j < k <= |numbers|
            {
                if CanFormTriplet(numbers[i], numbers[j], numbers[k]) {
                    triplets := triplets + [[numbers[i], numbers[j], numbers[k]]];
                }
                k := k + 1;
            }
            j := j + 1;
        }
        i := i + 1;
    }
    triplets
}

predicate IsValidTripletFromNumbers(triplet: seq<int>, numbers: seq<int>)
{
    |triplet| == 3 &&
    triplet[0] in numbers && triplet[1] in numbers && triplet[2] in numbers &&
    ValidTriplet(triplet)
}

function method RemoveElements(numbers: seq<int>, toRemove: seq<int>): seq<int>
{
    var result := numbers;
    var i := 0;
    while i < |toRemove|
        invariant 0 <= i <= |toRemove|
    {
        result := RemoveFirst(result, toRemove[i]);
        i := i + 1;
    }
    result
}

function method RemoveFirst(numbers: seq<int>, element: int): seq<int>
{
    if |numbers| == 0 then []
    else if numbers[0] == element then numbers[1..]
    else [numbers[0]] + RemoveFirst(numbers[1..], element)
}

lemma FlattenPartitionProperties(result: seq<seq<int>>)
    ensures |FlattenPartition(result)| == if |result| == 0 then 0 else |result[0]| + |FlattenPartition(result[1..])|
{
    if |result| == 0 {
    } else {
        FlattenPartitionProperties(result[1..]);
    }
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, numbers: seq<int>) returns (result: seq<seq<int>>)
    requires ValidInput(n, numbers)
    ensures NoPartitionExists(result) || ValidPartition(result, numbers)
// </vc-spec>
// <vc-code>
{
    if n == 0 {
        result := [];
        return;
    }
    
    var remaining := numbers;
    result := [];
    var targetTriplets := n / 3;
    
    while |result| < targetTriplets && |remaining| >= 3
        invariant 0 <= |result| <= targetTriplets
        invariant |remaining| >= 0
        invariant forall i :: 0 <= i < |result| ==> ValidTriplet(result[i])
    {
        var found := false;
        var i := 0;
        
        while i < |remaining| && !found
            invariant 0 <= i <= |remaining|
        {
            var j := i + 1;
            while j < |remaining| && !found
                invariant i < j <= |remaining|
            {
                var k := j + 1;
                while k < |remaining| && !found
                    invariant j < k <= |remaining|
                {
                    if CanFormTriplet(remaining[i], remaining[j], remaining[k]) {
                        var triplet := [remaining[i], remaining[j], remaining[k]];
                        result := result + [triplet];
                        
                        // Remove the used elements
                        var temp := remaining;
                        temp := RemoveFirst(temp, remaining[i]);
                        temp := RemoveFirst(temp, remaining[j]);
                        temp := RemoveFirst(temp, remaining[k]);
                        remaining := temp;
                        
                        found := true;
                    }
                    k := k + 1;
                }
                j := j + 1;
            }
            i := i + 1;
        }
        
        if !found {
            result := [];
            return;
        }
    }
    
    if |result| != targetTriplets || |remaining| != 0 {
        result := [];
    }
}
// </vc-code>

