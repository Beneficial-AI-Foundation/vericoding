// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function Contains(xs: seq<int>, x: int): bool {
    if |xs| == 0 then false else xs[0] == x || Contains(xs[1..], x)
}

lemma ContainsLemma(xs: seq<int>, x: int, y: int)
    requires Contains(xs, x)
    ensures Contains(xs + [y], x)
{
    if |xs| == 0 {
        // Contradiction with requirement
    } else if xs[0] == x {
        // x is at the head of xs
    } else {
        // x is in the tail of xs
        ContainsLemma(xs[1..], x, y);
    }
}
// </vc-helpers>

// <vc-spec>
method SetToSeq(s: seq<int>) returns (result: seq<int>)
    ensures
        // All elements are unique in the result  
        forall i: int, j: int :: 0 <= i < j < |result| ==> result[i] != result[j]
    ensures
        // Every element in result is in s
        forall i: int :: 0 <= i < |result| ==> 
            exists j: int :: 0 <= j < |s| && s[j] == result[i]
    ensures
        // Every element in s is in result
        forall i: int :: 0 <= i < |s| ==> 
            exists j: int :: 0 <= j < |result| && result[j] == s[i]
// </vc-spec>
// <vc-code>
{
    result := [];
    var i: int := 0;
    while i < |s|
        invariant 0 <= i <= |s|
        invariant forall j: int, k: int :: 0 <= j < k < |result| ==> result[j] != result[k]  // result is unique
        invariant forall j: int :: 0 <= j < |result| ==> exists k: int :: 0 <= k < i && s[k] == result[j]  // all elements in result are from s[0..i-1]
    {
        if !Contains(result, s[i]) {
            result := result + [s[i]];
        }
        i := i + 1;
    }
}
// </vc-code>
