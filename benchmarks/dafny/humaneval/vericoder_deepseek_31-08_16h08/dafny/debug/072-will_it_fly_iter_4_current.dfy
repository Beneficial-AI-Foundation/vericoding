

// <vc-helpers>
predicate is_palindrome_pred(s: seq<int>)
{
    forall k: int :: 0 <= k < |s| ==> s[k] == s[|s| - 1 - k]
}

function sum(s: seq<int>): int
    decreases |s|
{
    if |s| == 0 then 0 else s[0] + sum(s[1..])
}
// </vc-helpers>

// <vc-spec>
method will_it_fly(s: seq<int>, w: int) returns (result: bool)
    // pre-conditions-start
    requires |s| > 0
    // pre-conditions-end
    // post-conditions-start
    ensures result <==> is_palindrome_pred(s) && sum(s) <= w
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    var is_pal := true;
    var i: int := 0;
    var j: int := |s| - 1;
    var total: int := 0;
    
    while i < j
        invariant 0 <= i <= j + 1
        invariant j < |s|
        invariant i + j == |s| - 1
        invariant forall k: int :: 0 <= k < i ==> s[k] == s[|s| - 1 - k]
        invariant total == sum(s[0..i]) + sum(s[j+1..])
    {
        if s[i] != s[j] {
            is_pal := false;
        }
        total := total + s[i] + s[j];
        i := i + 1;
        j := j - 1;
    }
    
    if i == j {
        total := total + s[i];
    }
    
    result := is_pal && total <= w;
}
// </vc-code>

function is_palindrome_pred(s : seq<int>) : bool {
    forall k :: 0 <= k < |s| ==> s[k] == s[|s| - 1 - k]
}
// pure-end
function sum(s: seq<int>) : int {
    if |s| == 0 then 0 else s[0] + sum(s[1..])
}
// pure-end