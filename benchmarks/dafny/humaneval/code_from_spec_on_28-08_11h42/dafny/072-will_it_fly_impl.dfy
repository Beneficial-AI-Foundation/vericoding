// <vc-helpers>
lemma palindrome_check_equivalence(s: seq<int>)
    ensures is_palindrome_pred(s) <==> is_palindrome_iterative(s)
    decreases |s|
{
    if |s| <= 1 {
        assert is_palindrome_pred(s);
        assert is_palindrome_iterative(s);
    } else {
        palindrome_helper_correctness(s, 0);
    }
}

lemma palindrome_helper_correctness(s: seq<int>, i: int)
    requires 0 <= i <= |s| / 2
    ensures palindrome_helper(s, i) <==> (forall k :: i <= k < |s| / 2 ==> s[k] == s[|s| - 1 - k])
    ensures (forall k :: 0 <= k < |s| / 2 ==> s[k] == s[|s| - 1 - k]) <==> is_palindrome_pred(s)
    decreases |s| / 2 - i
{
    if i >= |s| / 2 {
        assert palindrome_helper(s, i);
        assert forall k :: i <= k < |s| / 2 ==> s[k] == s[|s| - 1 - k];
    } else {
        if s[i] != s[|s| - 1 - i] {
            assert !palindrome_helper(s, i);
            assert !(forall k :: i <= k < |s| / 2 ==> s[k] == s[|s| - 1 - k]);
        } else {
            palindrome_helper_correctness(s, i + 1);
        }
    }
}

function is_palindrome_iterative(s: seq<int>): bool
    decreases |s|
{
    if |s| <= 1 then true
    else palindrome_helper(s, 0)
}

function palindrome_helper(s: seq<int>, i: int): bool
    requires 0 <= i <= |s| / 2
    decreases |s| / 2 - i
{
    if i >= |s| / 2 then true
    else if s[i] != s[|s| - 1 - i] then false
    else palindrome_helper(s, i + 1)
}

function sum_iterative(s: seq<int>): int
    ensures sum_iterative(s) == sum(s)
{
    sum_iterative_helper(s, 0, 0)
}

function sum_iterative_helper(s: seq<int>, i: int, acc: int): int
    requires 0 <= i <= |s|
    ensures sum_iterative_helper(s, i, acc) == acc + sum(s[i..])
    decreases |s| - i
{
    if i >= |s| then acc
    else sum_iterative_helper(s, i + 1, acc + s[i])
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
    palindrome_check_equivalence(s);
    var is_pal := is_palindrome_iterative(s);
    var total := sum_iterative(s);
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