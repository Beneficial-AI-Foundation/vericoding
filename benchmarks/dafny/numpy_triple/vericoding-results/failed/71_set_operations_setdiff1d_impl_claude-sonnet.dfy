// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function isInSeq(val: int, s: seq<int>): bool
{
    exists i :: 0 <= i < |s| && s[i] == val
}

/* helper modified by LLM (iteration 5): Fixed sortSeq termination with explicit size bounds */
function removeDuplicates(s: seq<int>): seq<int>
    decreases |s|
{
    if |s| == 0 then []
    else if isInSeq(s[0], s[1..]) then removeDuplicates(s[1..])
    else [s[0]] + removeDuplicates(s[1..])
}

/* helper modified by LLM (iteration 5): Fixed partitioning to ensure smaller size for termination */
function sortSeq(s: seq<int>): seq<int>
    decreases |s|
    ensures |sortSeq(s)| == |s|
    ensures forall x :: x in s <==> x in sortSeq(s)
    ensures forall i, j :: 0 <= i < j < |sortSeq(s)| ==> sortSeq(s)[i] <= sortSeq(s)[j]
{
    if |s| <= 1 then s
    else 
        var pivot := s[0];
        var rest := s[1..];
        var smaller := seq(x | x in rest && x < pivot);
        var larger := seq(x | x in rest && x >= pivot);
        sortSeq(smaller) + [pivot] + sortSeq(larger)
}

function filter<T>(s: seq<T>, pred: T -> bool): seq<T>
    decreases |s|
    ensures |filter(s, pred)| <= |s|
    ensures forall x :: x in filter(s, pred) ==> x in s && pred(x)
{
    if |s| == 0 then []
    else if pred(s[0]) then [s[0]] + filter(s[1..], pred)
    else filter(s[1..], pred)
}

lemma SeqConstructionSize(rest: seq<int>, pivot: int)
    ensures |seq(x | x in rest && x < pivot)| < |rest| + 1
    ensures |seq(x | x in rest && x >= pivot)| < |rest| + 1
{
}
// </vc-helpers>

// <vc-spec>
method setdiff1d(ar1: seq<int>, ar2: seq<int>) returns (result: seq<int>)
    // Each element in result is from ar1 and not in ar2
    ensures forall i :: 0 <= i < |result| ==> 
        (exists j :: 0 <= j < |ar1| && result[i] == ar1[j]) &&
        (forall k :: 0 <= k < |ar2| ==> result[i] != ar2[k])
    
    // No duplicates in result
    ensures forall i, j :: 0 <= i < j < |result| ==> result[i] != result[j]
    
    // Result is sorted in ascending order
    ensures forall i, j :: 0 <= i < j < |result| ==> result[i] <= result[j]
    
    // All unique values from ar1 not in ar2 are included in result
    ensures forall val {:trigger val in ar1} :: 
        ((exists i :: 0 <= i < |ar1| && ar1[i] == val) && 
         (forall j :: 0 <= j < |ar2| ==> ar2[j] != val)) ==>
        (exists k :: 0 <= k < |result| && result[k] == val)
    
    // Completeness: result contains exactly the values that should be there
    ensures forall val :: 
        (val in result) <==> 
        (val in ar1 && val !in ar2)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed implementation with proper invariants and assertions */
    var temp: seq<int> := [];
    var i := 0;
    
    while i < |ar1|
        invariant 0 <= i <= |ar1|
        invariant forall j :: 0 <= j < |temp| ==> 
            (exists k :: 0 <= k < i && ar1[k] == temp[j]) &&
            (forall l :: 0 <= l < |ar2| ==> temp[j] != ar2[l])
        invariant forall x, y :: 0 <= x < y < |temp| ==> temp[x] != temp[y]
        invariant forall val :: val in temp ==> val in ar1 && val !in ar2
        invariant forall val :: 
            ((exists k :: 0 <= k < i && ar1[k] == val) && val !in ar2 && val !in temp) ==> 
            exists m :: 0 <= m < i && ar1[m] == val && val in temp
    {
        if !isInSeq(ar1[i], ar2) && !isInSeq(ar1[i], temp) {
            temp := temp + [ar1[i]];
        }
        i := i + 1;
    }
    
    // Prove completeness
    assert forall val :: 
        ((exists k :: 0 <= k < |ar1| && ar1[k] == val) && val !in ar2) ==> val in temp;
    
    result := sortSeq(temp);
    
    // Final assertions to help verification
    assert |result| == |temp|;
    assert forall x :: x in result <==> x in temp;
    assert forall val :: (val in result) <==> (val in ar1 && val !in ar2);
}
// </vc-code>
