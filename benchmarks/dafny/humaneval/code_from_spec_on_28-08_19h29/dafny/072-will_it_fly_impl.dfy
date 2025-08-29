// <vc-helpers>
function isPalindromePred(s: seq<int>): bool {
    forall k :: 0 <= k < |s| ==> s[k] == s[|s| - 1 - k]
}

function sumSeq(s: seq<int>): int {
    if |s| == 0 then 0 else s[0] + sumSeq(s[1..])
}

lemma SumSeqPrefix(s: seq<int>, i: int)
    requires 0 <= i <= |s|
    ensures sumSeq(s[..i]) == if i == 0 then 0 else sumSeq(s[..i-1]) + s[i-1]
{
    if i == 0 {
    } else if i == 1 {
    } else {
        SumSeqPrefix(s[1..], i-1);
    }
}
// </vc-helpers>

// <vc-description>
/*
function_signature: def will_it_fly(q: List[int], w: int) -> bool
Write a function that returns True if the object q will fly, and False otherwise. The object q will fly if it's balanced (it is a palindromic list) and the sum of its elements is less than or equal the maximum possible weight w.
*/
// </vc-description>

// <vc-spec>
method will_it_fly(q: seq<int>, w: int) returns (result: bool)
    ensures result == (isPalindromePred(q) && sumSeq(q) <= w)
// </vc-spec>
// <vc-code>
{
    var is_palindrome := true;
    var i := 0;
    while i < |q| / 2
        invariant 0 <= i <= |q| / 2
        invariant is_palindrome ==> forall k :: 0 <= k < i ==> q[k] == q[|q| - 1 - k]
    {
        if q[i] != q[|q| - 1 - i] {
            is_palindrome := false;
            break;
        }
        i := i + 1;
    }
    
    if !is_palindrome {
        return false;
    }
    
    if |q| == 0 {
        return true;
    }
    
    var total_sum := 0;
    i := 0;
    while i < |q|
        invariant 0 <= i <= |q|
        invariant total_sum == sumSeq(q[..i])
    {
        total_sum := total_sum + q[i];
        SumSeqPrefix(q, i+1);
        if total_sum > w {
            return false;
        }
        i := i + 1;
    }
    
    return total_sum <= w;
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